// Copyright © 2024 Manuel Rodríguez & Zero-Day Labs, Lda.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

// Licensed under the Solderpad Hardware License v 2.1 (the “License”); 
// you may not use this file except in compliance with the License, 
// or, at your option, the Apache License version 2.0. 
// You may obtain a copy of the License at https://solderpad.org/licenses/SHL-2.1/.
// Unless required by applicable law or agreed to in writing, 
// any work distributed under the License is distributed on an “AS IS” BASIS, 
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. 
// See the License for the specific language governing permissions and limitations under the License.
//
// Author: Manuel Rodríguez <manuel.cederog@gmail.com>
// Date: 02/03/2023
//
// Description: RISC-V SPMP Interface.
//

module spmp_interface #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg        = config_pkg::cva6_cfg_empty,
    parameter type                   icache_areq_t  = logic,
    parameter type                   icache_arsp_t  = logic,
    parameter type                   exception_t    = logic
) (
    input logic clk_i,
    input logic rst_ni,

    // CSR data
    input  riscv::priv_lvl_t priv_lvl_i,
    input  logic v_i,
    input  riscv::priv_lvl_t ld_st_priv_lvl_i,
    input  logic ld_st_v_i,
    input  logic sum_i,
    input  logic vs_sum_i,
    input  logic mxr_i,
    input  logic vmxr_i,
    input  logic hlvx_inst_i,
    input  logic mmu_enabled_i,

    // IF interface
    input icache_arsp_t if_req_i,
    output icache_areq_t if_req_o,

    // LSU interface
    input logic lsu_valid_i,
    input logic [CVA6Cfg.PLEN-1:0] lsu_vaddr_i,
    input logic [31:0] lsu_tinst_i,
    input logic lsu_is_store_i,
    input exception_t misaligned_ex_i,

    output logic lsu_valid_o,
    output logic [CVA6Cfg.PLEN-1:0] lsu_paddr_o,
    output exception_t lsu_exception_o,

    // SPMP CSRs
    input riscv::spmpcfg_t [(CVA6Cfg.NrSPMPEntries > 0 ? CVA6Cfg.NrSPMPEntries-1 : 0):0]  spmpcfg_i,
    input logic [(CVA6Cfg.NrSPMPEntries > 0 ? CVA6Cfg.NrSPMPEntries-1 : 0):0][CVA6Cfg.PLEN-3:0] spmpaddr_i,
    input logic [63:0] spmpswitch_i,
    input riscv::spmpcfg_t [(CVA6Cfg.NrSPMPEntries > 0 ? CVA6Cfg.NrSPMPEntries-1 : 0):0]  vspmpcfg_i,
    input logic [(CVA6Cfg.NrSPMPEntries > 0 ? CVA6Cfg.NrSPMPEntries-1 : 0):0][CVA6Cfg.PLEN-3:0] vspmpaddr_i,
    input logic [63:0] vspmpswitch_i
);

    //------------------------------------
    // SPMP Input Parameter Configuration
    //------------------------------------

    logic [CVA6Cfg.PLEN-1:0]  if_req_addr;
    riscv::pmp_access_t       if_access_type;
    riscv::priv_lvl_t         if_priv_lvl;
    logic                     if_v;
    
    logic [CVA6Cfg.PLEN-1:0]  lsu_req_addr;
    riscv::pmp_access_t       lsu_access_type;
    riscv::priv_lvl_t         lsu_priv_lvl;
    logic                     lsu_v;

    logic [CVA6Cfg.PLEN-1:0]  if_req_addr_q, if_req_addr_d;
    logic [CVA6Cfg.PLEN-1:0]  lsu_req_addr_q, lsu_req_addr_d;
    logic [31:0] lsu_tinst_q, lsu_tinst_d;
    logic if_v_q, if_v_d;
    logic lsu_v_q, lsu_v_d;
    exception_t misaligned_ex_q, misaligned_ex_d;
    logic if_req_q, if_req_d;
    logic ld_req_q, ld_req_d;
    logic st_req_q, st_req_d;

    always_comb begin : spmp_parameters

        // IF
        if_req_addr      = (CVA6Cfg.VLEN >= CVA6Cfg.PLEN) ?
                            (if_req_i.fetch_vaddr[CVA6Cfg.PLEN-1:0]) :
                            (CVA6Cfg.PLEN'(if_req_i.fetch_vaddr));
        if_access_type   = riscv::ACCESS_EXEC;
        if_priv_lvl      = priv_lvl_i;
        if_v             = v_i;

        // LSU
        lsu_req_addr     = (CVA6Cfg.VLEN >= CVA6Cfg.PLEN) ?
                            (lsu_vaddr_i[CVA6Cfg.PLEN-1:0]) :
                            (CVA6Cfg.PLEN'(lsu_vaddr_i));
        lsu_access_type  = riscv::ACCESS_NONE;
        lsu_priv_lvl     = ld_st_priv_lvl_i;
        lsu_v            = ld_st_v_i;

        if_req_addr_d   = if_req_addr;
        if_v_d          = v_i;
        lsu_req_addr_d  = lsu_req_addr;
        lsu_tinst_d     = lsu_tinst_i;
        lsu_v_d         = ld_st_v_i;
        misaligned_ex_d = misaligned_ex_i;
        if_req_d        = 1'b0;
        ld_req_d        = 1'b0;
        st_req_d        = 1'b0;

        /*** IF request ***/
        if (if_req_i.fetch_req) begin
            if_req_d        = 1'b1;
        end

        /*** Load request ***/
        if (lsu_valid_i && !lsu_is_store_i) begin
            ld_req_d        = 1'b1;
            lsu_access_type = riscv::ACCESS_READ;
        end

        /*** Store request ***/
        else if (lsu_valid_i && lsu_is_store_i) begin
            st_req_d        = 1'b1;
            lsu_access_type = riscv::ACCESS_WRITE;
        end
    end : spmp_parameters

    //-------------------------
    // SPMP Exception Handling
    //-------------------------

    logic [CVA6Cfg.XLEN-1:0]  lsu_ex_addr;
    logic [CVA6Cfg.GPLEN-1:0] lsu_ex_gpaddr;
    logic                     lsu_spmp_allow_q, lsu_spmp_allow_d;
    logic                     if_spmp_allow_q, if_spmp_allow_d;
    logic                     lsu_vspmp_allow_q, lsu_vspmp_allow_d;
    logic                     if_vspmp_allow_q, if_vspmp_allow_d;
    always_comb begin : spmp_exception

        // IF
        if_req_o.fetch_valid        = if_req_q;
        if_req_o.fetch_paddr        = if_req_addr_q;
        if_req_o.fetch_exception    = '0;

        // LSU
        lsu_valid_o     = (ld_req_q | st_req_q);
        lsu_paddr_o     = lsu_req_addr_q;
        lsu_exception_o = misaligned_ex_q;
        lsu_ex_addr     = (CVA6Cfg.VLEN > CVA6Cfg.PLEN)? 
                          {{8{1'b0}}, lsu_req_addr_q}:
                          (lsu_req_addr_q[CVA6Cfg.VLEN-1:0]);
        lsu_ex_gpaddr   = (CVA6Cfg.VLEN > CVA6Cfg.PLEN)? 
                          (lsu_req_addr_q[CVA6Cfg.GPLEN-1:0]):
                          {lsu_req_addr_q};

        /*** IF request ***/
        if (if_req_q) begin
            // SPMP Exception
            if (!if_spmp_allow_q) begin
                if_req_o.fetch_exception.cause  = riscv::INSTR_PAGE_FAULT;
                if_req_o.fetch_exception.tval   = (CVA6Cfg.VLEN > CVA6Cfg.PLEN)? 
                                                    {{8{1'b0}}, if_req_addr_q}:
                                                    (if_req_addr_q[CVA6Cfg.VLEN-1:0]);
                if_req_o.fetch_exception.gva    = if_v_q;
                if (if_v_q) begin
                    if_req_o.fetch_exception.cause = riscv::INSTR_GUEST_PAGE_FAULT;
                    if_req_o.fetch_exception.tval2 = (CVA6Cfg.VLEN > CVA6Cfg.PLEN)? 
                                                        (if_req_addr_q[CVA6Cfg.GPLEN-1:0]):
                                                        {if_req_addr_q};
                end
                if_req_o.fetch_exception.valid = if_req_i.fetch_req;
            end
            // vSPMP Exception
            else if (!if_vspmp_allow_q) begin
                if_req_o.fetch_exception.cause  = riscv::INSTR_PAGE_FAULT;
                if_req_o.fetch_exception.tval   = (CVA6Cfg.VLEN > CVA6Cfg.PLEN)? 
                                                    {{8{1'b0}}, if_req_addr_q}:
                                                    (if_req_addr_q[CVA6Cfg.VLEN-1:0]);
                if_req_o.fetch_exception.gva    = if_v_q;
                if_req_o.fetch_exception.valid = if_req_i.fetch_req;
            end
        end

        /*** Load request ***/
        if (ld_req_q) begin
            // SPMP Exception
            if (!lsu_spmp_allow_q) begin
                lsu_exception_o.cause  = (lsu_v_q) ? (riscv::LOAD_GUEST_PAGE_FAULT) : (riscv::LOAD_PAGE_FAULT);
                lsu_exception_o.tval   = lsu_ex_addr;
                lsu_exception_o.tval2  = (lsu_v_q) ? (lsu_ex_gpaddr) : ({CVA6Cfg.GPLEN{1'b0}});
                lsu_exception_o.tinst  = {32{1'b0}};
                lsu_exception_o.gva    = lsu_v_q;
                lsu_exception_o.valid  = 1'b1;
            end
            // vSPMP exception
            else if (!lsu_vspmp_allow_q) begin
                lsu_exception_o.cause  = riscv::LOAD_PAGE_FAULT;
                lsu_exception_o.tval   = lsu_ex_addr;
                lsu_exception_o.tval2  = {CVA6Cfg.GPLEN{1'b0}};
                lsu_exception_o.tinst  = lsu_tinst_q;
                lsu_exception_o.gva    = lsu_v_q;
                lsu_exception_o.valid  = 1'b1;
            end
        end

        /*** Store request ***/
        else if (st_req_q) begin
            // SPMP Exception
            if (!lsu_spmp_allow_q) begin
                lsu_exception_o.cause  = (lsu_v_q) ? (riscv::STORE_GUEST_PAGE_FAULT) : (riscv::STORE_PAGE_FAULT);
                lsu_exception_o.tval   = lsu_ex_addr;
                lsu_exception_o.tval2  = (lsu_v_q) ? (lsu_ex_gpaddr) : ({CVA6Cfg.GPLEN{1'b0}});
                lsu_exception_o.tinst  = {32{1'b0}};
                lsu_exception_o.gva    = lsu_v_q;
                lsu_exception_o.valid  = 1'b1;
            end
            // vSPMP exception
            else if (!lsu_vspmp_allow_q) begin
                lsu_exception_o.cause  = riscv::STORE_PAGE_FAULT;
                lsu_exception_o.tval   = lsu_ex_addr;
                lsu_exception_o.tval2  = {CVA6Cfg.GPLEN{1'b0}};
                lsu_exception_o.tinst  = lsu_tinst_q;
                lsu_exception_o.gva    = lsu_v_q;
                lsu_exception_o.valid  = 1'b1;
            end
        end
    end : spmp_exception

    //--------------------
    // SPMP Instantiation
    //--------------------

    // Double-stage SPMP
    if (CVA6Cfg.RVH) begin : gen_double_spmp

        // IF vSPMP
        spmp_hyp #(
            .CVA6Cfg            (CVA6Cfg),
            .is_vSPMP           (1)
        ) i_if_vspmp (
            .addr_i             (if_req_addr),
            .access_type_i      (if_access_type),
            .priv_lvl_i         (if_priv_lvl),
            .sum_i              (vs_sum_i),
            .mxr_i              (mxr_i),
            .vmxr_i             (vmxr_i),
            .v_i                (if_v),
            .is_hlvx_inst_i     (hlvx_inst_i),
            .mmu_enabled_i      (mmu_enabled_i),
            .spmpcfg_i          (vspmpcfg_i),
            .spmpaddr_i         (vspmpaddr_i),
            .spmpswitch_i       (vspmpswitch_i),
            .allow_o            (if_vspmp_allow_d)
        );

        // IF [hg]SPMP
        spmp_hyp #(
            .CVA6Cfg            (CVA6Cfg),
            .is_vSPMP           (0)
        ) i_if_spmp (
            .addr_i             (if_req_addr),
            .access_type_i      (if_access_type),
            .priv_lvl_i         (if_priv_lvl),
            .sum_i              (sum_i),
            .mxr_i              (mxr_i),
            .vmxr_i             (vmxr_i),
            .v_i                (if_v),
            .is_hlvx_inst_i     (hlvx_inst_i),
            .mmu_enabled_i      (mmu_enabled_i),
            .spmpcfg_i          (spmpcfg_i),
            .spmpaddr_i         (spmpaddr_i),
            .spmpswitch_i       (spmpswitch_i),
            .allow_o            (if_spmp_allow_d)
        );
            
        // LSU vSPMP
        spmp_hyp #(
            .CVA6Cfg            (CVA6Cfg),
            .is_vSPMP           (1)
        ) i_lsu_vspmp (
            .addr_i             (lsu_req_addr),
            .access_type_i      (lsu_access_type),
            .priv_lvl_i         (lsu_priv_lvl),
            .sum_i              (vs_sum_i),
            .mxr_i              (mxr_i),
            .vmxr_i             (vmxr_i),
            .v_i                (lsu_v),
            .is_hlvx_inst_i     (hlvx_inst_i),
            .mmu_enabled_i      (mmu_enabled_i),
            .spmpcfg_i          (vspmpcfg_i),
            .spmpaddr_i         (vspmpaddr_i),
            .spmpswitch_i       (vspmpswitch_i),
            .allow_o            (lsu_vspmp_allow_d)
        );

        // LSU [hg]SPMP
        spmp_hyp #(
            .CVA6Cfg            (CVA6Cfg),
            .is_vSPMP           (0)
        ) i_lsu_spmp (
            .addr_i             (lsu_req_addr),
            .access_type_i      (lsu_access_type),
            .priv_lvl_i         (lsu_priv_lvl),
            .sum_i              (sum_i),
            .mxr_i              (mxr_i),
            .vmxr_i             (vmxr_i),
            .v_i                (lsu_v),
            .is_hlvx_inst_i     (hlvx_inst_i),
            .mmu_enabled_i      (mmu_enabled_i),
            .spmpcfg_i          (spmpcfg_i),
            .spmpaddr_i         (spmpaddr_i),
            .spmpswitch_i       (spmpswitch_i),
            .allow_o            (lsu_spmp_allow_d)
        );
    end : gen_double_spmp

    // Single-stage SPMP
    else begin : gen_single_spmp
    
        // IF SPMP
        spmp #( 
            .CVA6Cfg            (CVA6Cfg)
        ) i_if_spmp (
            .addr_i             (if_req_addr),
            .access_type_i      (if_access_type),
            .priv_lvl_i         (if_priv_lvl),
            .sum_i              (sum_i),
            .mxr_i              (mxr_i),
            .mmu_enabled_i      (mmu_enabled_i),
            .spmpcfg_i          (spmpcfg_i),
            .spmpaddr_i         (spmpaddr_i),
            .spmpswitch_i       (spmpswitch_i),
            .allow_o            (if_spmp_allow_d)
        );

        // LSU SPMP
        spmp #( 
            .CVA6Cfg            (CVA6Cfg)
        ) i_lsu_spmp (
            .addr_i             (lsu_req_addr),
            .access_type_i      (lsu_access_type),
            .priv_lvl_i         (lsu_priv_lvl),
            .sum_i              (sum_i),
            .mxr_i              (mxr_i),
            .mmu_enabled_i      (mmu_enabled_i),
            .spmpcfg_i          (spmpcfg_i),
            .spmpaddr_i         (spmpaddr_i),
            .spmpswitch_i       (spmpswitch_i),
            .allow_o            (lsu_spmp_allow_d)
        );

        assign lsu_vspmp_allow_d = 1'b1;
        assign if_vspmp_allow_d = 1'b1;
    end : gen_single_spmp

    always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        if_req_q            <= 1'b0;
        ld_req_q            <= 1'b0;
        st_req_q            <= 1'b0;
        if_req_addr_q       <= '0;
        if_v_q              <= 1'b0;
        if_spmp_allow_q     <= 1'b1;
        if_vspmp_allow_q    <= 1'b1;
        lsu_req_addr_q      <= '0;
        lsu_tinst_q         <= '0;
        lsu_v_q             <= 1'b0;
        misaligned_ex_q     <= '0;
        lsu_spmp_allow_q    <= 1'b1;
        lsu_vspmp_allow_q   <= 1'b1;
    end else begin
        if_req_q            <= if_req_d;
        ld_req_q            <= ld_req_d;
        st_req_q            <= st_req_d;
        if_req_addr_q       <= if_req_addr_d;
        if_v_q              <= if_v_d;
        if_spmp_allow_q     <= if_spmp_allow_d;
        if_vspmp_allow_q    <= if_vspmp_allow_d;
        lsu_req_addr_q      <= lsu_req_addr_d;
        lsu_tinst_q         <= lsu_tinst_d;
        lsu_v_q             <= lsu_v_d;
        misaligned_ex_q     <= misaligned_ex_d;
        lsu_spmp_allow_q    <= lsu_spmp_allow_d;
        lsu_vspmp_allow_q   <= lsu_vspmp_allow_d;
    end
    end
endmodule