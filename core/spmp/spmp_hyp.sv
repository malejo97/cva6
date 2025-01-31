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
// Description: RISC-V SPMP for Hypervisor. Top module.
//
// Based on the PMP module developed by: Moritz Schneider (ETH Zurich) for the CVA6 core.
//

/*
    # is_vSPMP = 0
    To turn the SPMP virtualization-capable (and thus, perform checks as the hgPMP), we need to check the V bit.
    If V = 0, we consider S-mode and U-mode as it is in the table
    If V = 1, we consider VS and VU mode as U-mode in the table, and HS mode as S-mode in the table.

    In this case, we use the normal SPMP CSRs and sstatus.sum

    # is_vSPMP = 1
    For the vSPMP we consider VS-mode as S-mode and and VU-mode as U-mode in the table.
    In this case, we use the vSPMP CSRs and vsstatus.sum
*/

module spmp_hyp 
    import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,

    // [0] -> [hg]SPMP
    // [1] -> vSPMP
    parameter bit is_vSPMP = 0

) (
    // Access data
    input  logic [CVA6Cfg.PLEN-1:0] addr_i,
    input  riscv::pmp_access_t access_type_i,
    input  riscv::priv_lvl_t priv_lvl_i,
    // CSR data
    input  logic sum_i,
    input  logic mxr_i,
    input  logic vmxr_i,
    input  logic v_i,
    input  logic is_hlvx_inst_i,
    input  logic mmu_enabled_i,
    input  riscv::spmpcfg_t [(CVA6Cfg.NrSPMPEntries > 0 ? CVA6Cfg.NrSPMPEntries-1 : 0):0] spmpcfg_i,
    input  logic [(CVA6Cfg.NrSPMPEntries > 0 ? CVA6Cfg.NrSPMPEntries-1 : 0):0][CVA6Cfg.PLEN-3:0] spmpaddr_i,
    input  logic [63:0] spmpswitch_i,
    // Output
    output logic allow_o
);

    if (CVA6Cfg.NrSPMPEntries > 0) begin : gen_spmp

        //--------------------------
        // SPMP Address Match Logic
        //--------------------------

        logic [(CVA6Cfg.NrSPMPEntries-1):0] match;
        logic [(CVA6Cfg.NrSPMPEntries-1):0][CVA6Cfg.PLEN-3:0] spmpaddr_prev;

        for (genvar i = 0; i < CVA6Cfg.NrSPMPEntries; i++) begin : gen_spmp_matchers
            
            // Get previous address reg for TOR configs
            assign spmpaddr_prev[i] = ((i == 0) ? ('0) : (spmpaddr_i[i-1]));

            spmp_addr_matcher #(
                .CVA6Cfg            (CVA6Cfg)
            ) i_spmp_matcher (
                .addr_i             (addr_i),
                .spmpaddr_i         (spmpaddr_i[i]),
                .spmpaddr_prev_i    (spmpaddr_prev[i]),
                .matching_mode_i    (spmpcfg_i[i].addr_mode),
                .match_o            (match[i])
            );
        end : gen_spmp_matchers

        //------------------------------
        // SPMP Permissions Check Logic
        //------------------------------

        // Access type
        logic  access_R;
        logic  access_W;
        logic  access_X;
        logic  access_RW;

        assign access_R     = (access_type_i == riscv::ACCESS_READ);
        assign access_W     = (access_type_i == riscv::ACCESS_WRITE);
        assign access_X     = (access_type_i == riscv::ACCESS_EXEC);
        assign access_RW    = access_R | access_W;

        // Access privilege
        logic  access_S;
        logic  access_U;
        logic  access_HS;
        logic  access_M;

        assign access_U     = (priv_lvl_i == riscv::PRIV_LVL_U);
        assign access_S     = (priv_lvl_i == riscv::PRIV_LVL_S);
        assign access_M     = (priv_lvl_i == riscv::PRIV_LVL_M);

        // Efective privilege modes
        logic eff_Smode, eff_Umode;
        // Accesses to bypass
        logic bypass_check;
        // Permission check
        logic enforce, enforce_no_x;

        /* Determine effective privileges */
        if (is_vSPMP) begin : gen_vspmp
            // For the vSPMP we consider VS-mode as S-mode and and VU-mode as U-mode.
            assign eff_Smode  = access_S & v_i;
            assign eff_Umode  = access_U & v_i;
            // Bypass non-guest accesses
            assign bypass_check = !v_i;
        end : gen_vspmp

        else begin : gen_unif_spmp
            // In the unified SPMP model, we consider S/HS-mode as S-mode
            // If V = 0, we consider U-mode as Umode
            // If V = 1, we consider VS-mode and VU-mode as Umode
            assign eff_Smode  = access_HS | (access_S & !v_i);
            assign eff_Umode  = (v_i) ? (access_S | access_U)  : (access_U);
            // Bypass all M-mode accesses
            assign bypass_check = access_M;
        end : gen_unif_spmp

        always_comb begin : spmp_check

            int unsigned i;

            enforce         = 1'b0;
            enforce_no_x    = 1'b0;
            allow_o         = 1'b0;

            // All M-mode accesses pass SPMP cheks
            // If the core MMU is enabled (vsatp.mode/hgatp.mode != Bare), SPMP is not used
            if (bypass_check || mmu_enabled_i) begin
                allow_o = 1'b1;
            end

            else begin

                // SPMP entries are statically prioritized
                // The lowest-numbered SPMP matching entry determines whether the access is allowed or fails
                for (i = 0; i < CVA6Cfg.NrSPMPEntries; i++) begin

                    // Enforce checks
                    // Access is allowed if:
                    // (1) Permissions matches with access type, if not an HLVX instruction
                    // (2) Load and cfg.X = 1 and (sstatus.MXR = 1 or (vsstatus.MXR = 1 and is_vSPMP = 1))
                    // (3) HLVX instruction and cfg.X = 1
                    if ( (((access_type_i & spmpcfg_i[i].access_perm) == access_type_i) && !is_hlvx_inst_i) || 
                            (access_R && spmpcfg_i[i].access_perm.x && (mxr_i || is_hlvx_inst_i || (vmxr_i && is_vSPMP)))) begin
                        enforce = 1'b1;
                    end

                    // HLVX will always fail when enforcing checks with no X permissions
                    // MXR has no effect without X permissions
                    if (((access_type_i & {1'b0, spmpcfg_i[i].access_perm[1:0]}) == access_type_i) && !is_hlvx_inst_i) begin
                        enforce_no_x = 1'b1;
                    end

                    if (match[i] && spmpswitch_i[i]) begin

                        // S-mode only rule
                        if (spmpcfg_i[i].s_mode) begin
                            
                            // XWR
                            case (spmpcfg_i[i].access_perm)

                                // Enforce for S-mode, deny for U-mode 
                                3'b001,
                                3'b101,
                                3'b100,
                                3'b011: begin
                                    allow_o =   (eff_Smode & enforce);
                                end

                                // Reserved encoding
                                3'b000: begin
                                    allow_o =   1'b0;
                                end

                                // Shared RO
                                3'b111: begin
                                    allow_o =   (access_R);
                                end

                                // R for S-mode, Shared X
                                3'b110: begin
                                    allow_o =   (access_X) |
                                                (access_R & eff_Smode);
                                end

                                // Shared X
                                3'b010: begin
                                    allow_o =   (access_X);
                                end

                            endcase
                        end

                        // U-mode rule
                        else begin
                            
                            // XWR
                            case (spmpcfg_i[i].access_perm)

                                // Deny for S-mode if sstatus.SUM = 0,
                                // Enforce without X for S-mode if sstatus.SUM = 1,
                                // Enforce for U-mode
                                3'b001,
                                3'b101,
                                3'b100,
                                3'b000,
                                3'b011,
                                3'b111: begin
                                    allow_o =   (eff_Smode & sum_i & enforce_no_x) |  
                                                (eff_Umode & enforce);
                                end

                                // Shared RW
                                3'b110: begin
                                    allow_o =   (access_RW);
                                end

                                // Shared R, RW for S-mode
                                3'b010: begin
                                    allow_o =   (access_R) |
                                                (access_W & eff_Smode);
                                end
                            endcase
                        end

                        // No need to continue after a match
                        break;
                    end
                end

                // no match
                if (i == CVA6Cfg.NrSPMPEntries) begin

                    // If no SPMP entry matches, the following accesses are allowed:
                    // M/HS/U/VS-mode accesses if is_vSPMP = 1
                    // M/HS-mode accesses if is_vSPMP = 0
                    allow_o = eff_Smode;
                end
            end
        end : spmp_check

    end : gen_spmp
    
    // if there are no SPMP entries we can always grant the access
    else
        assign allow_o = 1'b1;

endmodule