// Copyright © 2025 Manuel Rodríguez & Zero-Day Labs, Lda.
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
// Date: 02/03/2024
//
// Description: RISC-V SPMP top module.
//
// Based on the PMP module developed by: Moritz Schneider (ETH Zurich) for the CVA6 core.
//

module spmp 
    import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty
) (
    // Access data
    input logic [CVA6Cfg.PLEN-1:0] addr_i,
    input riscv::pmp_access_t access_type_i,
    input riscv::priv_lvl_t priv_lvl_i,
    // CSR data
    input  logic sum_i,
    input  logic mxr_i,
    input  logic mmu_enabled_i,
    input riscv::spmpcfg_t [(CVA6Cfg.NrSPMPEntries > 0 ? CVA6Cfg.NrSPMPEntries-1 : 0):0] spmpcfg_i,
    input logic [(CVA6Cfg.NrSPMPEntries > 0 ? CVA6Cfg.NrSPMPEntries-1 : 0):0][CVA6Cfg.PLEN-3:0] spmpaddr_i,
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

        logic  access_R;
        logic  access_X;
        logic  access_RW;

        assign access_R     = (access_type_i == riscv::ACCESS_READ);
        assign access_W     = (access_type_i == riscv::ACCESS_WRITE);
        assign access_X     = (access_type_i == riscv::ACCESS_EXEC);
        assign access_RW    = access_R | access_W;

        logic enforce, enforce_no_x;

        always_comb begin : spmp_check

            int unsigned i;

            enforce         = 1'b0;
            enforce_no_x    = 1'b0;
            allow_o         = 1'b0;

            // All M-mode accesses pass SPMP cheks
            // If the core MMU is enabled (satp.mode != Bare), SPMP is not used
            if ((priv_lvl_i == riscv::PRIV_LVL_M) || mmu_enabled_i) begin
                allow_o = 1'b1;
            end

            else begin
                // SPMP entries are statically prioritized
                // The lowest-numbered SPMP matching entry determines whether the access is allowed or fails
                for (i = 0; i < CVA6Cfg.NrSPMPEntries; i++) begin

                    // Enforce permission checks
                    // mstatus.mxr makes loads succeed with executable permissions
                    enforce         = (((access_type_i & spmpcfg_i[i].access_perm) == access_type_i) |
                                       (access_R & spmpcfg_i[i].access_perm.x & mxr_i));
                    // Enforce permission checks without X permissions
                    enforce_no_x    = ((access_type_i & {1'b0, spmpcfg_i[i].access_perm[1:0]}) == access_type_i);

                    if (match[i]) begin

                        // S-mode only rule
                        if (spmpcfg_i[i].s_mode) begin
                            
                            // XWR
                            unique case (spmpcfg_i[i].access_perm)

                                // Enforce for S-mode, deny for U-mode 
                                3'b001,
                                3'b101,
                                3'b100,
                                3'b011: begin
                                    allow_o =   ((priv_lvl_i == riscv::PRIV_LVL_S) & enforce);
                                end

                                // Reserved encoding
                                3'b000: begin
                                    allow_o =   1'b0;
                                end

                                // Shared RO
                                3'b111: begin
                                    allow_o =   (access_R);
                                end

                                // RX for S-mode, X for U-mode
                                3'b110: begin
                                    allow_o =   (access_X) |
                                                (access_R & (priv_lvl_i == riscv::PRIV_LVL_S));
                                end

                                // Shared X
                                3'b010: begin
                                    allow_o =   (access_X);
                                end
                            endcase
                        end

                        // U-mode only rule or shared region
                        else begin
                            
                            // XWR
                            unique case (spmpcfg_i[i].access_perm)

                                // Deny for S-mode if sstatus.SUM = 0,
                                // Enforce without X for S-mode if sstatus.SUM = 1,
                                // Enforce for U-mode 
                                3'b001,
                                3'b101,
                                3'b100,
                                3'b000,
                                3'b011,
                                3'b111: begin
                                    allow_o =   (priv_lvl_i == riscv::PRIV_LVL_S) ? 
                                                (sum_i & enforce_no_x) : 
                                                (enforce);
                                end

                                // Shared RW
                                3'b110: begin
                                    allow_o =   (access_RW);
                                end

                                // R for U-mode, RW for S-mode
                                3'b010: begin
                                    allow_o =   (access_R) |
                                                (access_W & (priv_lvl_i == riscv::PRIV_LVL_S));
                                end
                            endcase
                        end

                        // No need to continue after a match
                        break;
                    end
                end

                // no match
                if (i == CVA6Cfg.NrSPMPEntries) begin

                    // If no SPMP entry matches, only M-mode and S-mode accesses are allowed
                    allow_o = (priv_lvl_i == riscv::PRIV_LVL_S);
                end
            end
        end : spmp_check
    end : gen_spmp
    
    // if there are no SPMP entries we can always grant the access
    else
        assign allow_o = 1'b1;

endmodule