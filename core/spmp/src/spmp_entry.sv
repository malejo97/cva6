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
// Date: 05/03/2024
//
// Description: RISC-V SPMP entry matching logic.
//
// Based on the PMP entry module developed by Moritz Schneider (ETH Zurich) for the CVA6 core.
//

// TODO: Should we signal when an SPMP entry spans only part of the memory access ?
// TODO: Spec defines that these accesses should fail

module spmp_entry #(
    parameter int unsigned PLEN = 56
) (
    // Input
    input logic [PLEN-1:0]          addr_i,

    // Configuration
    input riscv::spmpaddr_t         spmpaddr_i,
    input riscv::spmpaddr_t         spmpaddr_prev_i,
    input riscv::pmp_addr_mode_t    matching_mode_i,

    // Output
    output logic                    match_o
);

    logic [PLEN-1:0] conf_addr_n;
    logic [$clog2(PLEN)-1:0] trail_ones;
    logic [PLEN-1:0] base_addr;
    logic [PLEN-1:0] mask;
    // 2 for G = 0
    // 3 for G = 1
    // 4 for G = 4, etc
    int unsigned size;

    assign conf_addr_n = {2'b11, ~spmpaddr_i};

    lzc #(
        .WIDTH(PLEN),
        .MODE (1'b0)                // Count trailing zeros
    ) i_lzc (
        .in_i    ( conf_addr_n ),   // Input addr
        .cnt_o   ( trail_ones  ),   // Number of trailing ones (from the LSb)
        .empty_o (             )
    );

    always_comb begin

        size        = '0;
        base_addr   = '0;
        mask        = '0;

        case (matching_mode_i)

            riscv::TOR: begin

                base_addr   = '0;
                mask        = '0;
                size        = '0;
                // check that the requested address is in between the two config addresses
                if (addr_i >= ({2'b0, spmpaddr_prev_i} << 2) && addr_i < ({2'b0, spmpaddr_i} << 2)) begin
                    match_o = 1'b1;
                end
                
                else
                    match_o = 1'b0;
            end

            riscv::NA4,
            riscv::NAPOT: begin
                
            if (matching_mode_i == riscv::NA4)
                size = 2;
            else begin
                // use the extracted trailing ones
                size = {{(32 - $clog2(PLEN)) {1'b0}}, trail_ones} + 3;
            end

                mask        = ('1 << size);
                base_addr   = ({2'b0, spmpaddr_i} << 2) & mask;
                match_o     = ((addr_i & mask) == base_addr);
            end

            riscv::OFF: begin
                match_o     = 1'b0;
                base_addr   = '0;
                mask        = '0;
                size        = '0;
            end

            default: begin
                match_o     = 1'b0;
                base_addr   = '0;
                mask        = '0;
                size        = '0;
            end
        endcase
    end

endmodule
