// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 06.10.2017
// Description: Performance counters


module perf_counters
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type bp_resolve_t = logic,
    parameter type dcache_req_i_t = logic,
    parameter type dcache_req_o_t = logic,
    parameter type exception_t = logic,
    parameter type icache_dreq_t = logic,
    parameter type scoreboard_entry_t = logic,
    parameter int unsigned NumPorts = 3  // number of miss ports
) (
    input logic clk_i,
    input logic rst_ni,
    input logic debug_mode_i,  // debug mode
    input riscv::priv_lvl_t priv_lvl_i, // current CPU privilege mode
    input logic v_i, //  current CPU virtualization mode
    // SRAM like interface
    input logic [11:0] addr_i,  // read/write address (up to 6 counters possible)
    input logic we_i,  // write enable
    input logic [CVA6Cfg.XLEN-1:0] data_i,  // data to write
    output logic [CVA6Cfg.XLEN-1:0] data_o,  // data to read
    // single-cycle overflow signal
    output logic [MHPMCounterNum-1:0] counter_of_o,
    // mhpmevent.OF signal
    output logic [MHPMCounterNum-1:0] mhpmevent_of_o,
    // from commit stage
    input  scoreboard_entry_t [CVA6Cfg.NrCommitPorts-1:0] commit_instr_i,     // the instruction we want to commit
    input  logic [CVA6Cfg.NrCommitPorts-1:0]              commit_ack_i,       // acknowledge that we are indeed committing
    // from L1 caches
    input logic l1_icache_miss_i,
    input logic l1_dcache_miss_i,
    // from MMU
    input logic itlb_miss_i,
    input logic dtlb_miss_i,
    // from issue stage
    input logic sb_full_i,
    // from frontend
    input logic if_empty_i,
    // from PC Gen
    input exception_t ex_i,
    input logic eret_i,
    input bp_resolve_t resolved_branch_i,
    // for newly added events
    input exception_t branch_exceptions_i,  //Branch exceptions->execute unit-> branch_exception_o
    input icache_dreq_t l1_icache_access_i,
    input dcache_req_i_t [2:0] l1_dcache_access_i,
    input  logic [NumPorts-1:0][CVA6Cfg.DCACHE_SET_ASSOC-1:0]miss_vld_bits_i,  //For Cache eviction (3ports-LOAD,STORE,PTW)
    input logic i_tlb_flush_i,
    input logic stall_issue_i,  //stall-read operands
    input logic [31:0] mcountinhibit_i
);

  typedef logic [11:0] csr_addr_t;

  typedef enum int unsigned {
    XINH_WPRI1 = 56,
    XINH_WPRI2 = 57,
    VUINH = 58,
    VSINH = 59,
    UINH = 60,
    SINH = 61,
    MINH = 62,
    OF = 63
  } mhpmevent_xinh_t;

  logic [63:0] generic_counter_d[MHPMCounterNum:1];
  logic [63:0] generic_counter_q[MHPMCounterNum:1];

  //internal signal to keep track of exception
  logic read_access_exception, update_access_exception;

  logic events[6:1];
  //internal signal for  MUX select line input
  logic [63:0] mhpmevent_d[MHPMCounterNum:1];
  logic [63:0] mhpmevent_q[MHPMCounterNum:1];
  // internal signal to detect event on multiple commit ports
  logic [CVA6Cfg.NrCommitPorts-1:0] load_event;
  logic [CVA6Cfg.NrCommitPorts-1:0] store_event;
  logic [CVA6Cfg.NrCommitPorts-1:0] branch_event;
  logic [CVA6Cfg.NrCommitPorts-1:0] call_event;
  logic [CVA6Cfg.NrCommitPorts-1:0] return_event;
  logic [CVA6Cfg.NrCommitPorts-1:0] int_event;
  logic [CVA6Cfg.NrCommitPorts-1:0] fp_event;

  // Overflow signaling
  logic [MHPMCounterNum-1:0] counter_of_d, counter_of_q;
  assign counter_of_o = counter_of_q;

  // Privilege-based inhibition
  logic [MHPMCounterNum-1:0] priv_inh;

  // Access privilege
  logic access_M;
  logic access_S;
  logic access_U;
  logic access_VS;
  logic access_VU;

  assign access_M = (priv_lvl_i == riscv::PRIV_LVL_M);
  assign access_S = (((priv_lvl_i == riscv::PRIV_LVL_S) && !v_i) || (priv_lvl_i == riscv::PRIV_LVL_HS));
  assign access_U = ((priv_lvl_i == riscv::PRIV_LVL_U) && !v_i);
  assign access_VS = ((priv_lvl_i == riscv::PRIV_LVL_S) && v_i);
  assign access_VU = ((priv_lvl_i == riscv::PRIV_LVL_U) && v_i);

  for (genvar i = 1; i <= MHPMCounterNum; i++) begin
    assign priv_inh[i-1] = (mhpmevent_q[i][MINH] & access_M)    |
                            (mhpmevent_q[i][SINH] & access_S)   |
                            (mhpmevent_q[i][UINH] & access_U)   |
                            (mhpmevent_q[i][VSINH] & access_VS) |
                            (mhpmevent_q[i][VUINH] & access_VU);
    assign mhpmevent_of_o[i-1] = mhpmevent_q[i][OF];
  end

  //Multiplexer
  always_comb begin : Mux
    events[MHPMCounterNum:1] = '{default: 0};
    load_event = '{default: 0};
    store_event = '{default: 0};
    branch_event = '{default: 0};
    call_event = '{default: 0};
    return_event = '{default: 0};
    int_event = '{default: 0};
    fp_event = '{default: 0};

    for (int unsigned j = 0; j < CVA6Cfg.NrCommitPorts; j++) begin
      load_event[j] = commit_ack_i[j] & (commit_instr_i[j].fu == LOAD);
      store_event[j] = commit_ack_i[j] & (commit_instr_i[j].fu == STORE);
      branch_event[j] = commit_ack_i[j] & (commit_instr_i[j].fu == CTRL_FLOW);
      call_event[j] = commit_ack_i[j] & (commit_instr_i[j].fu == CTRL_FLOW && (commit_instr_i[j].op == ADD || commit_instr_i[j].op == JALR) && (commit_instr_i[j].rd == 'd1 || commit_instr_i[j].rd == 'd5));
      return_event[j] = commit_ack_i[j] & (commit_instr_i[j].op == JALR && commit_instr_i[j].rd == 'd0);
      int_event[j] = commit_ack_i[j] & (commit_instr_i[j].fu == ALU || commit_instr_i[j].fu == MULT);
      fp_event[j] = commit_ack_i[j] & (commit_instr_i[j].fu == FPU || commit_instr_i[j].fu == FPU_VEC);
    end

    for (int unsigned i = 1; i <= MHPMCounterNum; i++) begin
      case (mhpmevent_q[i][4:0])
        /* SBI-DEFINED EVENTS */
        5'b00000: events[i] = 0;
        5'b00001: events[i] = 1;  //CPU Cycle
        5'b00010: events[i] = |commit_ack_i;  //Completed instruction
        5'b00011: 
        events[i] = ((l1_dcache_access_i[0].data_req | l1_dcache_access_i[1].data_req | l1_dcache_access_i[2].data_req) & ~l1_dcache_miss_i) |
                    (l1_icache_access_i.req & ~l1_icache_miss_i); //Cache hit
        5'b00100: events[i] = l1_dcache_miss_i | l1_icache_miss_i;  //Cache misses
        5'b00101: events[i] = |branch_event;  // Branch instructions
        5'b00110: events[i] = resolved_branch_i.valid && resolved_branch_i.is_mispredict;//Branch mispredicts
        5'b00111: events[i] = 0;
        5'b01000: events[i] = 0;
        5'b01001: events[i] = 0;
        5'b01010: events[i] = 0;
        /*** PLATFORM-DEFINED EVENTS ***/
        5'b01011: events[i] = ex_i.valid;  //Exceptions
        5'b01100: events[i] = eret_i;  //Exception handler returns
        5'b01101: events[i] = |load_event;  //Load accesses
        5'b01110: events[i] = |store_event;  //Store accesses
        5'b01111: events[i] = branch_exceptions_i.valid;  //Branch exceptions
        // The standard software calling convention uses register x1 to hold the return address on a call
        // the unconditional jump is decoded as ADD op
        5'b10000: events[i] = |call_event;  //Call
        5'b10001: events[i] = |return_event;  //Return
        5'b10010: events[i] = sb_full_i;  //MSB Full
        5'b10011: events[i] = if_empty_i;  //Instruction fetch Empty
        5'b10100: events[i] = dtlb_miss_i;  //DTLB misses
        5'b10101: events[i] = itlb_miss_i;  //ITLB misses
        5'b10110:
        events[i] = (l1_dcache_miss_i && miss_vld_bits_i[0] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[1] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[2] == 8'hFF);//eviction
        5'b10111: events[i] = i_tlb_flush_i;  //I-TLB flush
        5'b11000: events[i] = |int_event;  //Integer instructions
        5'b11001: events[i] = |fp_event;  //Floating Point Instructions
        5'b11010: events[i] = stall_issue_i;  //Pipeline bubbles
        default: events[i] = 0;
      endcase
    end

  end

  always_comb begin : generic_counter
    generic_counter_d = generic_counter_q;
    counter_of_d = '0;
    data_o = 'b0;
    mhpmevent_d = mhpmevent_q;
    read_access_exception = 1'b0;
    update_access_exception = 1'b0;

    // Increment the non-inhibited counters with active events
    for (int unsigned i = 1; i <= MHPMCounterNum; i++) begin
      if ((!debug_mode_i) && (!we_i)) begin
        if ((events[i] == 1) && (!mcountinhibit_i[i+2]) && (!priv_inh[i-1])) begin
          generic_counter_d[i] = generic_counter_q[i] + 1'b1;
          if (((&(generic_counter_q[i])) == 1'b1) && (!(mhpmevent_q[i][OF]))) begin
            counter_of_d[i-1] = 1'b1;
            mhpmevent_d[i][OF] = 1'b1;
          end
        end
      end
    end

    //Read
    if( (addr_i >= csr_addr_t'(riscv::CSR_MHPM_COUNTER_3)) && (addr_i < ( csr_addr_t'(riscv::CSR_MHPM_COUNTER_3) + MHPMCounterNum)) ) begin
      if (riscv::XLEN == 32) begin
        data_o = generic_counter_q[addr_i-riscv::CSR_MHPM_COUNTER_3+1][31:0];
      end else begin
        data_o = generic_counter_q[addr_i-riscv::CSR_MHPM_COUNTER_3+1];
      end
    end else if( (addr_i >= csr_addr_t'(riscv::CSR_MHPM_COUNTER_3H)) && (addr_i < ( csr_addr_t'(riscv::CSR_MHPM_COUNTER_3H) + MHPMCounterNum)) ) begin
      if (riscv::XLEN == 32) begin
        data_o = generic_counter_q[addr_i-riscv::CSR_MHPM_COUNTER_3H+1][63:32];
      end else begin
        read_access_exception = 1'b1;
      end
    end else if( (addr_i >= csr_addr_t'(riscv::CSR_MHPM_EVENT_3)) && (addr_i < (csr_addr_t'(riscv::CSR_MHPM_EVENT_3) + MHPMCounterNum)) ) begin
      if (riscv::XLEN == 32) begin
        data_o = mhpmevent_q[addr_i-riscv::CSR_MHPM_EVENT_3+1][31:0];
      end else begin
        data_o = mhpmevent_q[addr_i-riscv::CSR_MHPM_EVENT_3+1];
      end
    end else if( (addr_i >= csr_addr_t'(riscv::CSR_MHPM_EVENT_3H)) && (addr_i < ( csr_addr_t'(riscv::CSR_MHPM_EVENT_3H) + MHPMCounterNum)) ) begin
      if (riscv::XLEN == 32) begin
        data_o = mhpmevent_q[addr_i-riscv::CSR_MHPM_EVENT_3H+1][63:32];
      end else begin
        read_access_exception = 1'b1;
      end
    end else if( (addr_i >= csr_addr_t'(riscv::CSR_HPM_COUNTER_3)) && (addr_i < (csr_addr_t'(riscv::CSR_HPM_COUNTER_3) + MHPMCounterNum)) ) begin
      if (riscv::XLEN == 32) begin
        data_o = generic_counter_q[addr_i-riscv::CSR_HPM_COUNTER_3+1][31:0];
      end else begin
        data_o = generic_counter_q[addr_i-riscv::CSR_HPM_COUNTER_3+1];
      end
    end else if( (addr_i > csr_addr_t'(riscv::CSR_HPM_COUNTER_3H)) && (addr_i < (csr_addr_t'(riscv::CSR_HPM_COUNTER_3H) + MHPMCounterNum)) ) begin
      if (riscv::XLEN == 32) begin
        data_o = generic_counter_q[addr_i-riscv::CSR_MHPM_COUNTER_3H+1][63:32];
      end else begin
        read_access_exception = 1'b1;
      end
    end

    //Write
    if (we_i) begin
      if( (addr_i >= csr_addr_t'(riscv::CSR_MHPM_COUNTER_3)) && (addr_i < (csr_addr_t'(riscv::CSR_MHPM_COUNTER_3) + MHPMCounterNum)) ) begin
        if (riscv::XLEN == 32) begin
          generic_counter_d[addr_i-riscv::CSR_MHPM_COUNTER_3+1][31:0] = data_i;
        end else begin
          generic_counter_d[addr_i-riscv::CSR_MHPM_COUNTER_3+1] = data_i;
        end
      end else if( (addr_i >= csr_addr_t'(riscv::CSR_MHPM_COUNTER_3H)) && (addr_i < (csr_addr_t'(riscv::CSR_MHPM_COUNTER_3H) + MHPMCounterNum)) ) begin
        if (riscv::XLEN == 32) begin
          generic_counter_d[addr_i-riscv::CSR_MHPM_COUNTER_3H+1][63:32] = data_i;
        end else begin
          update_access_exception = 1'b1;
        end
      end else if( (addr_i >= csr_addr_t'(riscv::CSR_MHPM_EVENT_3)) && (addr_i < csr_addr_t'(riscv::CSR_MHPM_EVENT_3) + MHPMCounterNum) ) begin
        if (riscv::XLEN == 32) begin
          mhpmevent_d[addr_i-riscv::CSR_MHPM_EVENT_3+1][31:0] = data_i;
        end else begin
          mhpmevent_d[addr_i-riscv::CSR_MHPM_EVENT_3+1] = data_i;
        end
      end else if( (addr_i >= csr_addr_t'(riscv::CSR_MHPM_EVENT_3H)) && (addr_i < (csr_addr_t'(riscv::CSR_MHPM_EVENT_3H) + MHPMCounterNum)) ) begin
        if (riscv::XLEN == 32) begin
          mhpmevent_d[addr_i-riscv::CSR_MHPM_EVENT_3H+1][63:32] = data_i;
        end else begin
          update_access_exception = 1'b1;
        end
      end
    end
  end

  //Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      generic_counter_q <= '{default: 0};
      mhpmevent_q       <= '{default: 0};
      counter_of_q      <= '{default: 0};
    end else begin
      generic_counter_q <= generic_counter_d;
      mhpmevent_q       <= mhpmevent_d;
      counter_of_q      <= counter_of_d;
    end
  end

endmodule
