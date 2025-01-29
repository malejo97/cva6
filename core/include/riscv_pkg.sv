/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   riscv_pkg.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   30.6.2017
 *
 * Description: Common RISC-V definitions.
 */

package riscv;

  // ----------------------
  // Import cva6 config from cva6_config_pkg
  // ----------------------
  // FIXME stop using them from CoreV-Verif and HPDCache
  // Then remove them from this package
  localparam XLEN = cva6_config_pkg::CVA6ConfigXlen;
  localparam PLEN = (XLEN == 32) ? 34 : 56;

  // --------------------
  // Privilege Spec
  // --------------------
  typedef enum logic [1:0] {
    PRIV_LVL_M  = 2'b11,
    PRIV_LVL_HS = 2'b10,
    PRIV_LVL_S  = 2'b01,
    PRIV_LVL_U  = 2'b00
  } priv_lvl_t;

  // type which holds xlen
  typedef enum logic [1:0] {
    XLEN_32  = 2'b01,
    XLEN_64  = 2'b10,
    XLEN_128 = 2'b11
  } xlen_e;

  typedef enum logic [1:0] {
    Off     = 2'b00,
    Initial = 2'b01,
    Clean   = 2'b10,
    Dirty   = 2'b11
  } xs_t;

  typedef struct packed {
    logic sd;  // signal dirty state - read-only
    logic [62:34] wpri6;  // writes preserved reads ignored
    xlen_e uxl;  // variable user mode xlen - hardwired to zero
    logic [11:0] wpri5;  // writes preserved reads ignored
    logic mxr;  // make executable readable
    logic sum;  // permit supervisor user memory access
    logic wpri4;  // writes preserved reads ignored
    xs_t xs;  // extension register - hardwired to zero
    xs_t fs;  // floating point extension register
    logic [1:0] wpri3;  // writes preserved reads ignored
    xs_t vs;  // vector extension register
    logic spp;  // holds the previous privilege mode up to supervisor
    logic wpri2;  // writes preserved reads ignored
    logic mpie;  // machine interrupts enable bit active prior to trap
    logic         ube;    // UBE controls whether explicit load and store memory accesses made from U-mode are little-endian (UBE=0) or big-endian (UBE=1)
    logic spie;  // supervisor interrupts enable bit active prior to trap
    logic [2:0] wpri1;  // writes preserved reads ignored
    logic sie;  // supervisor interrupts enable
    logic wpri0;  // writes preserved reads ignored
  } sstatus_rv_t;

  typedef struct packed {
    logic [63:34] wpri4;  // writes preserved reads ignored
    xlen_e        vsxl;   // variable virtual supervisor mode xlen - hardwired to zero
    logic [8:0]   wpri3;  // floating point extension register
    logic         vtsr;   // virtual trap sret
    logic         vtw;    // virtual time wait
    logic         vtvm;   // virtual trap virtual memory
    logic [1:0]   wpri2;  // writes preserved reads ignored
    logic [5:0]   vgein;  // virtual guest external interrupt number
    logic [1:0]   wpri1;  // writes preserved reads ignored
    logic         hu;     // virtual-machine load/store instructions enable in U-mode
    logic         spvp;   // supervisor previous virtual privilege
    logic         spv;    // supervisor previous virtualization mode
    logic         gva;    // variable set when trap writes to stval
    logic         vsbe;   // endianness of explicit memory accesses made from VS-mode
    logic [4:0]   wpri0;  // writes preserved reads ignored
  } hstatus_rv_t;

  typedef struct packed {
    logic sd;  // signal dirty state - read-only
    logic [62:40] wpri4;  // writes preserved reads ignored
    logic mpv;  // machine previous virtualization mode
    logic gva;  // variable set when trap writes to stval
    logic mbe;  // endianness memory accesses made from M-mode
    logic sbe;  // endianness memory accesses made from S-mode
    xlen_e sxl;  // variable supervisor mode xlen - hardwired to zero
    xlen_e uxl;  // variable user mode xlen - hardwired to zero
    logic [8:0] wpri3;  // writes preserved reads ignored
    logic tsr;  // trap sret
    logic tw;  // time wait
    logic tvm;  // trap virtual memory
    logic mxr;  // make executable readable
    logic sum;  // permit supervisor user memory access
    logic mprv;  // modify privilege - privilege level for ld/st
    xs_t xs;  // extension register - hardwired to zero
    xs_t fs;  // floating point extension register
    priv_lvl_t mpp;  // holds the previous privilege mode up to machine
    xs_t vs;  // vector extension register
    logic spp;  // holds the previous privilege mode up to supervisor
    logic mpie;  // machine interrupts enable bit active prior to trap
    logic         ube;    // UBE controls whether explicit load and store memory accesses made from U-mode are little-endian (UBE=0) or big-endian (UBE=1)
    logic spie;  // supervisor interrupts enable bit active prior to trap
    logic wpri2;  // writes preserved reads ignored
    logic mie;  // machine interrupts enable
    logic wpri1;  // writes preserved reads ignored
    logic sie;  // supervisor interrupts enable
    logic wpri0;  // writes preserved reads ignored
  } mstatus_rv_t;

  typedef struct packed {
    logic        stce;   // not implemented - requires Sctc extension
    logic        pbmte;  // not implemented - requires Svpbmt extension
    logic [61:8] wpri1;  // writes preserved reads ignored
    logic        cbze;   // not implemented - requires Zicboz extension
    logic        cbcfe;  // not implemented - requires Zicbom extension
    logic [1:0]  cbie;   // not implemented - requires Zicbom extension
    logic [2:0]  wpri0;  // writes preserved reads ignored
    logic        fiom;   // fence of I/O implies memory
  } envcfg_rv_t;

  // --------------------
  // Instruction Types
  // --------------------
  typedef struct packed {
    logic [31:25] funct7;
    logic [24:20] rs2;
    logic [19:15] rs1;
    logic [14:12] funct3;
    logic [11:7]  rd;
    logic [6:0]   opcode;
  } rtype_t;

  typedef struct packed {
    logic [31:27] rs3;
    logic [26:25] funct2;
    logic [24:20] rs2;
    logic [19:15] rs1;
    logic [14:12] funct3;
    logic [11:7]  rd;
    logic [6:0]   opcode;
  } r4type_t;

  typedef struct packed {
    logic [31:27] funct5;
    logic [26:25] fmt;
    logic [24:20] rs2;
    logic [19:15] rs1;
    logic [14:12] rm;
    logic [11:7]  rd;
    logic [6:0]   opcode;
  } rftype_t;  // floating-point

  typedef struct packed {
    logic [31:30] funct2;
    logic [29:25] vecfltop;
    logic [24:20] rs2;
    logic [19:15] rs1;
    logic [14:14] repl;
    logic [13:12] vfmt;
    logic [11:7]  rd;
    logic [6:0]   opcode;
  } rvftype_t;  // vectorial floating-point

  typedef struct packed {
    logic [31:20] imm;
    logic [19:15] rs1;
    logic [14:12] funct3;
    logic [11:7]  rd;
    logic [6:0]   opcode;
  } itype_t;

  typedef struct packed {
    logic [31:25] imm;
    logic [24:20] rs2;
    logic [19:15] rs1;
    logic [14:12] funct3;
    logic [11:7]  imm0;
    logic [6:0]   opcode;
  } stype_t;

  typedef struct packed {
    logic [31:12] imm;
    logic [11:7]  rd;
    logic [6:0]   opcode;
  } utype_t;

  // atomic instructions
  typedef struct packed {
    logic [31:27] funct5;
    logic         aq;
    logic         rl;
    logic [24:20] rs2;
    logic [19:15] rs1;
    logic [14:12] funct3;
    logic [11:7]  rd;
    logic [6:0]   opcode;
  } atype_t;

  typedef union packed {
    logic [31:0] instr;
    rtype_t      rtype;
    r4type_t     r4type;
    rftype_t     rftype;
    rvftype_t    rvftype;
    itype_t      itype;
    stype_t      stype;
    utype_t      utype;
    atype_t      atype;
  } instruction_t;

  // --------------------
  // Opcodes
  // --------------------
  // RV32/64G listings:
  // Quadrant 0
  localparam OpcodeLoad = 7'b00_000_11;
  localparam OpcodeLoadFp = 7'b00_001_11;
  localparam OpcodeCustom0 = 7'b00_010_11;
  localparam OpcodeMiscMem = 7'b00_011_11;
  localparam OpcodeOpImm = 7'b00_100_11;
  localparam OpcodeAuipc = 7'b00_101_11;
  localparam OpcodeOpImm32 = 7'b00_110_11;
  // Quadrant 1
  localparam OpcodeStore = 7'b01_000_11;
  localparam OpcodeStoreFp = 7'b01_001_11;
  localparam OpcodeCustom1 = 7'b01_010_11;
  localparam OpcodeAmo = 7'b01_011_11;
  localparam OpcodeOp = 7'b01_100_11;
  localparam OpcodeLui = 7'b01_101_11;
  localparam OpcodeOp32 = 7'b01_110_11;
  // Quadrant 2
  localparam OpcodeMadd = 7'b10_000_11;
  localparam OpcodeMsub = 7'b10_001_11;
  localparam OpcodeNmsub = 7'b10_010_11;
  localparam OpcodeNmadd = 7'b10_011_11;
  localparam OpcodeOpFp = 7'b10_100_11;
  localparam OpcodeVec = 7'b10_101_11;
  localparam OpcodeCustom2 = 7'b10_110_11;
  // Quadrant 3
  localparam OpcodeBranch = 7'b11_000_11;
  localparam OpcodeJalr = 7'b11_001_11;
  localparam OpcodeRsrvd2 = 7'b11_010_11;
  localparam OpcodeJal = 7'b11_011_11;
  localparam OpcodeSystem = 7'b11_100_11;
  localparam OpcodeRsrvd3 = 7'b11_101_11;
  localparam OpcodeCustom3 = 7'b11_110_11;

  // RV64C/RV32C listings:
  // Quadrant 0
  localparam OpcodeC0 = 2'b00;
  localparam OpcodeC0Addi4spn = 3'b000;
  localparam OpcodeC0Fld = 3'b001;
  localparam OpcodeC0Lw = 3'b010;
  localparam OpcodeC0Ld = 3'b011;
  localparam OpcodeC0Zcb = 3'b100;
  localparam OpcodeC0Fsd = 3'b101;
  localparam OpcodeC0Sw = 3'b110;
  localparam OpcodeC0Sd = 3'b111;
  // Quadrant 1
  localparam OpcodeC1 = 2'b01;
  localparam OpcodeC1Addi = 3'b000;
  localparam OpcodeC1Addiw = 3'b001;  //for RV64I only
  localparam OpcodeC1Jal = 3'b001;  //for RV32I only
  localparam OpcodeC1Li = 3'b010;
  localparam OpcodeC1LuiAddi16sp = 3'b011;
  localparam OpcodeC1MiscAlu = 3'b100;
  localparam OpcodeC1J = 3'b101;
  localparam OpcodeC1Beqz = 3'b110;
  localparam OpcodeC1Bnez = 3'b111;
  // Quadrant 2
  localparam OpcodeC2 = 2'b10;
  localparam OpcodeC2Slli = 3'b000;
  localparam OpcodeC2Fldsp = 3'b001;
  localparam OpcodeC2Lwsp = 3'b010;
  localparam OpcodeC2Ldsp = 3'b011;
  localparam OpcodeC2JalrMvAdd = 3'b100;
  localparam OpcodeC2Fsdsp = 3'b101;
  localparam OpcodeC2Swsp = 3'b110;
  localparam OpcodeC2Sdsp = 3'b111;

  // ----------------------
  // Virtual Memory
  // ----------------------
  // memory management, pte for sv39
  typedef struct packed {
    logic [9:0] reserved;
    logic [44-1:0] ppn;  // PPN length for
    logic [1:0] rsw;
    logic d;
    logic a;
    logic g;
    logic u;
    logic x;
    logic w;
    logic r;
    logic v;
  } pte_t;

  // memory management, pte for sv32
  typedef struct packed {
    logic [22-1:0] ppn;  // PPN length for
    logic [1:0] rsw;
    logic d;
    logic a;
    logic g;
    logic u;
    logic x;
    logic w;
    logic r;
    logic v;
  } pte_sv32_t;

  // ----------------------
  // Exception Cause Codes
  // ----------------------
  localparam logic [XLEN-1:0] INSTR_ADDR_MISALIGNED = 0;
  localparam logic [XLEN-1:0] INSTR_ACCESS_FAULT    = 1;  // Illegal access as governed by PMPs and PMAs
  localparam logic [XLEN-1:0] ILLEGAL_INSTR = 2;
  localparam logic [XLEN-1:0] BREAKPOINT = 3;
  localparam logic [XLEN-1:0] LD_ADDR_MISALIGNED = 4;
  localparam logic [XLEN-1:0] LD_ACCESS_FAULT = 5;  // Illegal access as governed by PMPs and PMAs
  localparam logic [XLEN-1:0] ST_ADDR_MISALIGNED = 6;
  localparam logic [XLEN-1:0] ST_ACCESS_FAULT = 7;  // Illegal access as governed by PMPs and PMAs
  localparam logic [XLEN-1:0] ENV_CALL_UMODE = 8;  // environment call from user mode or virtual user mode
  localparam logic [XLEN-1:0] ENV_CALL_SMODE = 9;  // environment call from hypervisor-extended supervisor mode
  localparam logic [XLEN-1:0] ENV_CALL_VSMODE = 10; // environment call from virtual supervisor mode
  localparam logic [XLEN-1:0] ENV_CALL_MMODE = 11;  // environment call from machine mode
  localparam logic [XLEN-1:0] INSTR_PAGE_FAULT = 12;  // Instruction page fault
  localparam logic [XLEN-1:0] LOAD_PAGE_FAULT = 13;  // Load page fault
  localparam logic [XLEN-1:0] STORE_PAGE_FAULT = 15;  // Store page fault
  localparam logic [XLEN-1:0] INSTR_GUEST_PAGE_FAULT = 20;  // Instruction guest-page fault
  localparam logic [XLEN-1:0] LOAD_GUEST_PAGE_FAULT = 21;  // Load guest-page fault
  localparam logic [XLEN-1:0] VIRTUAL_INSTRUCTION = 22;  // virtual instruction
  localparam logic [XLEN-1:0] STORE_GUEST_PAGE_FAULT = 23;  // Store guest-page fault
  localparam logic [XLEN-1:0] DEBUG_REQUEST = 24;  // Debug request

  localparam int unsigned IRQ_S_SOFT = 1;
  localparam int unsigned IRQ_VS_SOFT = 2;
  localparam int unsigned IRQ_M_SOFT = 3;
  localparam int unsigned IRQ_S_TIMER = 5;
  localparam int unsigned IRQ_VS_TIMER = 6;
  localparam int unsigned IRQ_M_TIMER = 7;
  localparam int unsigned IRQ_S_EXT = 9;
  localparam int unsigned IRQ_VS_EXT = 10;
  localparam int unsigned IRQ_M_EXT = 11;
  localparam int unsigned IRQ_HS_EXT = 12;

  localparam logic [31:0] MIP_SSIP = 1 << IRQ_S_SOFT;
  localparam logic [31:0] MIP_VSSIP = 1 << IRQ_VS_SOFT;
  localparam logic [31:0] MIP_MSIP = 1 << IRQ_M_SOFT;
  localparam logic [31:0] MIP_STIP = 1 << IRQ_S_TIMER;
  localparam logic [31:0] MIP_VSTIP = 1 << IRQ_VS_TIMER;
  localparam logic [31:0] MIP_MTIP = 1 << IRQ_M_TIMER;
  localparam logic [31:0] MIP_SEIP = 1 << IRQ_S_EXT;
  localparam logic [31:0] MIP_VSEIP = 1 << IRQ_VS_EXT;
  localparam logic [31:0] MIP_MEIP = 1 << IRQ_M_EXT;
  localparam logic [31:0] MIP_SGEIP = 1 << IRQ_HS_EXT;

  // ----------------------
  // PseudoInstructions Codes
  // ----------------------
  localparam logic [31:0] READ_32_PSEUDOINSTRUCTION = 32'h00002000;
  localparam logic [31:0] WRITE_32_PSEUDOINSTRUCTION = 32'h00002020;
  localparam logic [31:0] READ_64_PSEUDOINSTRUCTION = 32'h00003000;
  localparam logic [31:0] WRITE_64_PSEUDOINSTRUCTION = 32'h00003020;

  // -----
  // CSRs
  // -----
  typedef enum logic [11:0] {
    // Floating-Point CSRs
    CSR_FFLAGS           = 12'h001,
    CSR_FRM              = 12'h002,
    CSR_FCSR             = 12'h003,
    CSR_FTRAN            = 12'h800,
    // Vector CSRs
    CSR_VSTART           = 12'h008,
    CSR_VXSAT            = 12'h009,
    CSR_VXRM             = 12'h00A,
    CSR_VCSR             = 12'h00F,
    CSR_VL               = 12'hC20,
    CSR_VTYPE            = 12'hC21,
    CSR_VLENB            = 12'hC22,
    // Virtual Supervisor Mode CSRs
    CSR_VSSTATUS         = 12'h200,
    CSR_VSIE             = 12'h204,
    CSR_VSTVEC           = 12'h205,
    CSR_VSSCRATCH        = 12'h240,
    CSR_VSEPC            = 12'h241,
    CSR_VSCAUSE          = 12'h242,
    CSR_VSTVAL           = 12'h243,
    CSR_VSIP             = 12'h244,
    CSR_VSATP            = 12'h280,
    CSR_VSPMPCFG0        = 12'hA00,   // vSPMP Cfg
    CSR_VSPMPCFG1        = 12'hA01,
    CSR_VSPMPCFG2        = 12'hA02,
    CSR_VSPMPCFG3        = 12'hA03,
    CSR_VSPMPCFG4        = 12'hA04,
    CSR_VSPMPCFG5        = 12'hA05,
    CSR_VSPMPCFG6        = 12'hA06,
    CSR_VSPMPCFG7        = 12'hA07,
    CSR_VSPMPCFG8        = 12'hA08,
    CSR_VSPMPCFG9        = 12'hA09,
    CSR_VSPMPCFG10       = 12'hA0a,
    CSR_VSPMPCFG11       = 12'hA0b,
    CSR_VSPMPCFG12       = 12'hA0c,
    CSR_VSPMPCFG13       = 12'hA0d,
    CSR_VSPMPCFG14       = 12'hA0e,
    CSR_VSPMPCFG15       = 12'hA0f,
    CSR_VSPMPADDR0       = 12'hA10,   // vSPMP Addr
    CSR_VSPMPADDR1       = 12'hA11,
    CSR_VSPMPADDR2       = 12'hA12,
    CSR_VSPMPADDR3       = 12'hA13,
    CSR_VSPMPADDR4       = 12'hA14,
    CSR_VSPMPADDR5       = 12'hA15,
    CSR_VSPMPADDR6       = 12'hA16,
    CSR_VSPMPADDR7       = 12'hA17,
    CSR_VSPMPADDR8       = 12'hA18,
    CSR_VSPMPADDR9       = 12'hA19,
    CSR_VSPMPADDR10      = 12'hA1a,
    CSR_VSPMPADDR11      = 12'hA1b,
    CSR_VSPMPADDR12      = 12'hA1c,
    CSR_VSPMPADDR13      = 12'hA1d,
    CSR_VSPMPADDR14      = 12'hA1e,
    CSR_VSPMPADDR15      = 12'hA1f,
    CSR_VSPMPADDR16      = 12'hA20,
    CSR_VSPMPADDR17      = 12'hA21,
    CSR_VSPMPADDR18      = 12'hA22,
    CSR_VSPMPADDR19      = 12'hA23,
    CSR_VSPMPADDR20      = 12'hA24,
    CSR_VSPMPADDR21      = 12'hA25,
    CSR_VSPMPADDR22      = 12'hA26,
    CSR_VSPMPADDR23      = 12'hA27,
    CSR_VSPMPADDR24      = 12'hA28,
    CSR_VSPMPADDR25      = 12'hA29,
    CSR_VSPMPADDR26      = 12'hA2a,
    CSR_VSPMPADDR27      = 12'hA2b,
    CSR_VSPMPADDR28      = 12'hA2c,
    CSR_VSPMPADDR29      = 12'hA2d,
    CSR_VSPMPADDR30      = 12'hA2e,
    CSR_VSPMPADDR31      = 12'hA2f,
    CSR_VSPMPADDR32      = 12'hA30,
    CSR_VSPMPADDR33      = 12'hA31,
    CSR_VSPMPADDR34      = 12'hA32,
    CSR_VSPMPADDR35      = 12'hA33,
    CSR_VSPMPADDR36      = 12'hA34,
    CSR_VSPMPADDR37      = 12'hA35,
    CSR_VSPMPADDR38      = 12'hA36,
    CSR_VSPMPADDR39      = 12'hA37,
    CSR_VSPMPADDR40      = 12'hA38,
    CSR_VSPMPADDR41      = 12'hA39,
    CSR_VSPMPADDR42      = 12'hA3a,
    CSR_VSPMPADDR43      = 12'hA3b,
    CSR_VSPMPADDR44      = 12'hA3c,
    CSR_VSPMPADDR45      = 12'hA3d,
    CSR_VSPMPADDR46      = 12'hA3e,
    CSR_VSPMPADDR47      = 12'hA3f,
    CSR_VSPMPADDR48      = 12'hA40,
    CSR_VSPMPADDR49      = 12'hA41,
    CSR_VSPMPADDR50      = 12'hA42,
    CSR_VSPMPADDR51      = 12'hA43,
    CSR_VSPMPADDR52      = 12'hA44,
    CSR_VSPMPADDR53      = 12'hA45,
    CSR_VSPMPADDR54      = 12'hA46,
    CSR_VSPMPADDR55      = 12'hA47,
    CSR_VSPMPADDR56      = 12'hA48,
    CSR_VSPMPADDR57      = 12'hA49,
    CSR_VSPMPADDR58      = 12'hA4a,
    CSR_VSPMPADDR59      = 12'hA4b,
    CSR_VSPMPADDR60      = 12'hA4c,
    CSR_VSPMPADDR61      = 12'hA4d,
    CSR_VSPMPADDR62      = 12'hA4e,
    CSR_VSPMPADDR63      = 12'hA4f,
    CSR_VSPMPSWITCH0     = 12'hA50,   // vSPMP Switch
    CSR_VSPMPSWITCH1     = 12'hA51,
    // Supervisor Mode CSRs
    CSR_SSTATUS          = 12'h100,
    CSR_SIE              = 12'h104,
    CSR_STVEC            = 12'h105,
    CSR_SCOUNTEREN       = 12'h106,
    CSR_SENVCFG          = 12'h10A,
    CSR_SSCRATCH         = 12'h140,
    CSR_SEPC             = 12'h141,
    CSR_SCAUSE           = 12'h142,
    CSR_STVAL            = 12'h143,
    CSR_SIP              = 12'h144,
    CSR_SATP             = 12'h180,
    CSR_SPMPCFG0         = 12'h500,   // SPMP Cfg
    CSR_SPMPCFG1         = 12'h501,
    CSR_SPMPCFG2         = 12'h502,
    CSR_SPMPCFG3         = 12'h503,
    CSR_SPMPCFG4         = 12'h504,
    CSR_SPMPCFG5         = 12'h505,
    CSR_SPMPCFG6         = 12'h506,
    CSR_SPMPCFG7         = 12'h507,
    CSR_SPMPCFG8         = 12'h508,
    CSR_SPMPCFG9         = 12'h509,
    CSR_SPMPCFG10        = 12'h50A,
    CSR_SPMPCFG11        = 12'h50B,
    CSR_SPMPCFG12        = 12'h50C,
    CSR_SPMPCFG13        = 12'h50D,
    CSR_SPMPCFG14        = 12'h50E,
    CSR_SPMPCFG15        = 12'h50F,
    CSR_SPMPADDR0        = 12'h510,   // SPMP Addr
    CSR_SPMPADDR1        = 12'h511,
    CSR_SPMPADDR2        = 12'h512,
    CSR_SPMPADDR3        = 12'h513,
    CSR_SPMPADDR4        = 12'h514,
    CSR_SPMPADDR5        = 12'h515,
    CSR_SPMPADDR6        = 12'h516,
    CSR_SPMPADDR7        = 12'h517,
    CSR_SPMPADDR8        = 12'h518,
    CSR_SPMPADDR9        = 12'h519,
    CSR_SPMPADDR10       = 12'h51A,
    CSR_SPMPADDR11       = 12'h51B,
    CSR_SPMPADDR12       = 12'h51C,
    CSR_SPMPADDR13       = 12'h51D,
    CSR_SPMPADDR14       = 12'h51E,
    CSR_SPMPADDR15       = 12'h51F,
    CSR_SPMPADDR16       = 12'h520,
    CSR_SPMPADDR17       = 12'h521,
    CSR_SPMPADDR18       = 12'h522,
    CSR_SPMPADDR19       = 12'h523,
    CSR_SPMPADDR20       = 12'h524,
    CSR_SPMPADDR21       = 12'h525,
    CSR_SPMPADDR22       = 12'h526,
    CSR_SPMPADDR23       = 12'h527,
    CSR_SPMPADDR24       = 12'h528,
    CSR_SPMPADDR25       = 12'h529,
    CSR_SPMPADDR26       = 12'h52A,
    CSR_SPMPADDR27       = 12'h52B,
    CSR_SPMPADDR28       = 12'h52C,
    CSR_SPMPADDR29       = 12'h52D,
    CSR_SPMPADDR30       = 12'h52E,
    CSR_SPMPADDR31       = 12'h52F,
    CSR_SPMPADDR32       = 12'h530,
    CSR_SPMPADDR33       = 12'h531,
    CSR_SPMPADDR34       = 12'h532,
    CSR_SPMPADDR35       = 12'h533,
    CSR_SPMPADDR36       = 12'h534,
    CSR_SPMPADDR37       = 12'h535,
    CSR_SPMPADDR38       = 12'h536,
    CSR_SPMPADDR39       = 12'h537,
    CSR_SPMPADDR40       = 12'h538,
    CSR_SPMPADDR41       = 12'h539,
    CSR_SPMPADDR42       = 12'h53A,
    CSR_SPMPADDR43       = 12'h53B,
    CSR_SPMPADDR44       = 12'h53C,
    CSR_SPMPADDR45       = 12'h53D,
    CSR_SPMPADDR46       = 12'h53E,
    CSR_SPMPADDR47       = 12'h53F,
    CSR_SPMPADDR48       = 12'h540,
    CSR_SPMPADDR49       = 12'h541,
    CSR_SPMPADDR50       = 12'h542,
    CSR_SPMPADDR51       = 12'h543,
    CSR_SPMPADDR52       = 12'h544,
    CSR_SPMPADDR53       = 12'h545,
    CSR_SPMPADDR54       = 12'h546,
    CSR_SPMPADDR55       = 12'h547,
    CSR_SPMPADDR56       = 12'h548,
    CSR_SPMPADDR57       = 12'h549,
    CSR_SPMPADDR58       = 12'h54A,
    CSR_SPMPADDR59       = 12'h54B,
    CSR_SPMPADDR60       = 12'h54C,
    CSR_SPMPADDR61       = 12'h54D,
    CSR_SPMPADDR62       = 12'h54E,
    CSR_SPMPADDR63       = 12'h54F,
    CSR_SPMPSWITCH0      = 12'h550,   // SPMP Switch
    CSR_SPMPSWITCH1      = 12'h551,
    // Hypervisor-extended Supervisor Mode CSRs
    CSR_HSTATUS          = 12'h600,
    CSR_HEDELEG          = 12'h602,
    CSR_HIDELEG          = 12'h603,
    CSR_HIE              = 12'h604,
    CSR_HCOUNTEREN       = 12'h606,
    CSR_HGEIE            = 12'h607,
    CSR_HTVAL            = 12'h643,
    CSR_HIP              = 12'h644,
    CSR_HVIP             = 12'h645,
    CSR_HTINST           = 12'h64A,
    CSR_HGEIP            = 12'hE12,
    CSR_HENVCFG          = 12'h60A,
    CSR_HENVCFGH         = 12'h61A,
    CSR_HGATP            = 12'h680,
    CSR_HCONTEXT         = 12'h6A8,
    CSR_HTIMEDELTA       = 12'h605,
    CSR_HTIMEDELTAH      = 12'h615,
    // Machine Mode CSRs
    CSR_MSTATUS          = 12'h300,
    CSR_MISA             = 12'h301,
    CSR_MEDELEG          = 12'h302,
    CSR_MIDELEG          = 12'h303,
    CSR_MIE              = 12'h304,
    CSR_MTVEC            = 12'h305,
    CSR_MCOUNTEREN       = 12'h306,
    CSR_MSTATUSH         = 12'h310,
    CSR_MCOUNTINHIBIT    = 12'h320,
    CSR_MHPM_EVENT_3     = 12'h323,  //Machine performance monitoring Event Selector
    CSR_MHPM_EVENT_4     = 12'h324,  //Machine performance monitoring Event Selector
    CSR_MHPM_EVENT_5     = 12'h325,  //Machine performance monitoring Event Selector
    CSR_MHPM_EVENT_6     = 12'h326,  //Machine performance monitoring Event Selector
    CSR_MHPM_EVENT_7     = 12'h327,  //Machine performance monitoring Event Selector
    CSR_MHPM_EVENT_8     = 12'h328,  //Machine performance monitoring Event Selector
    CSR_MHPM_EVENT_9     = 12'h329,  //Reserved
    CSR_MHPM_EVENT_10    = 12'h32A,  //Reserved
    CSR_MHPM_EVENT_11    = 12'h32B,  //Reserved
    CSR_MHPM_EVENT_12    = 12'h32C,  //Reserved
    CSR_MHPM_EVENT_13    = 12'h32D,  //Reserved
    CSR_MHPM_EVENT_14    = 12'h32E,  //Reserved
    CSR_MHPM_EVENT_15    = 12'h32F,  //Reserved
    CSR_MHPM_EVENT_16    = 12'h330,  //Reserved
    CSR_MHPM_EVENT_17    = 12'h331,  //Reserved
    CSR_MHPM_EVENT_18    = 12'h332,  //Reserved
    CSR_MHPM_EVENT_19    = 12'h333,  //Reserved
    CSR_MHPM_EVENT_20    = 12'h334,  //Reserved
    CSR_MHPM_EVENT_21    = 12'h335,  //Reserved
    CSR_MHPM_EVENT_22    = 12'h336,  //Reserved
    CSR_MHPM_EVENT_23    = 12'h337,  //Reserved
    CSR_MHPM_EVENT_24    = 12'h338,  //Reserved
    CSR_MHPM_EVENT_25    = 12'h339,  //Reserved
    CSR_MHPM_EVENT_26    = 12'h33A,  //Reserved
    CSR_MHPM_EVENT_27    = 12'h33B,  //Reserved
    CSR_MHPM_EVENT_28    = 12'h33C,  //Reserved
    CSR_MHPM_EVENT_29    = 12'h33D,  //Reserved
    CSR_MHPM_EVENT_30    = 12'h33E,  //Reserved
    CSR_MHPM_EVENT_31    = 12'h33F,  //Reserved
    CSR_MSCRATCH         = 12'h340,
    CSR_MEPC             = 12'h341,
    CSR_MCAUSE           = 12'h342,
    CSR_MTVAL            = 12'h343,
    CSR_MIP              = 12'h344,
    CSR_MTINST           = 12'h34A,
    CSR_MTVAL2           = 12'h34B,
    CSR_MENVCFG          = 12'h30A,
    CSR_MENVCFGH         = 12'h31A,
    CSR_PMPCFG0          = 12'h3A0,
    CSR_PMPCFG1          = 12'h3A1,
    CSR_PMPCFG2          = 12'h3A2,
    CSR_PMPCFG3          = 12'h3A3,
    CSR_PMPCFG4          = 12'h3A4,
    CSR_PMPCFG5          = 12'h3A5,
    CSR_PMPCFG6          = 12'h3A6,
    CSR_PMPCFG7          = 12'h3A7,
    CSR_PMPCFG8          = 12'h3A8,
    CSR_PMPCFG9          = 12'h3A9,
    CSR_PMPCFG10         = 12'h3AA,
    CSR_PMPCFG11         = 12'h3AB,
    CSR_PMPCFG12         = 12'h3AC,
    CSR_PMPCFG13         = 12'h3AD,
    CSR_PMPCFG14         = 12'h3AE,
    CSR_PMPCFG15         = 12'h3AF,
    CSR_PMPADDR0         = 12'h3B0,
    CSR_PMPADDR1         = 12'h3B1,
    CSR_PMPADDR2         = 12'h3B2,
    CSR_PMPADDR3         = 12'h3B3,
    CSR_PMPADDR4         = 12'h3B4,
    CSR_PMPADDR5         = 12'h3B5,
    CSR_PMPADDR6         = 12'h3B6,
    CSR_PMPADDR7         = 12'h3B7,
    CSR_PMPADDR8         = 12'h3B8,
    CSR_PMPADDR9         = 12'h3B9,
    CSR_PMPADDR10        = 12'h3BA,
    CSR_PMPADDR11        = 12'h3BB,
    CSR_PMPADDR12        = 12'h3BC,
    CSR_PMPADDR13        = 12'h3BD,
    CSR_PMPADDR14        = 12'h3BE,
    CSR_PMPADDR15        = 12'h3BF,
    CSR_PMPADDR16        = 12'h3C0,
    CSR_PMPADDR17        = 12'h3C1,
    CSR_PMPADDR18        = 12'h3C2,
    CSR_PMPADDR19        = 12'h3C3,
    CSR_PMPADDR20        = 12'h3C4,
    CSR_PMPADDR21        = 12'h3C5,
    CSR_PMPADDR22        = 12'h3C6,
    CSR_PMPADDR23        = 12'h3C7,
    CSR_PMPADDR24        = 12'h3C8,
    CSR_PMPADDR25        = 12'h3C9,
    CSR_PMPADDR26        = 12'h3CA,
    CSR_PMPADDR27        = 12'h3CB,
    CSR_PMPADDR28        = 12'h3CC,
    CSR_PMPADDR29        = 12'h3CD,
    CSR_PMPADDR30        = 12'h3CE,
    CSR_PMPADDR31        = 12'h3CF,
    CSR_PMPADDR32        = 12'h3D0,
    CSR_PMPADDR33        = 12'h3D1,
    CSR_PMPADDR34        = 12'h3D2,
    CSR_PMPADDR35        = 12'h3D3,
    CSR_PMPADDR36        = 12'h3D4,
    CSR_PMPADDR37        = 12'h3D5,
    CSR_PMPADDR38        = 12'h3D6,
    CSR_PMPADDR39        = 12'h3D7,
    CSR_PMPADDR40        = 12'h3D8,
    CSR_PMPADDR41        = 12'h3D9,
    CSR_PMPADDR42        = 12'h3DA,
    CSR_PMPADDR43        = 12'h3DB,
    CSR_PMPADDR44        = 12'h3DC,
    CSR_PMPADDR45        = 12'h3DD,
    CSR_PMPADDR46        = 12'h3DE,
    CSR_PMPADDR47        = 12'h3DF,
    CSR_PMPADDR48        = 12'h3E0,
    CSR_PMPADDR49        = 12'h3E1,
    CSR_PMPADDR50        = 12'h3E2,
    CSR_PMPADDR51        = 12'h3E3,
    CSR_PMPADDR52        = 12'h3E4,
    CSR_PMPADDR53        = 12'h3E5,
    CSR_PMPADDR54        = 12'h3E6,
    CSR_PMPADDR55        = 12'h3E7,
    CSR_PMPADDR56        = 12'h3E8,
    CSR_PMPADDR57        = 12'h3E9,
    CSR_PMPADDR58        = 12'h3EA,
    CSR_PMPADDR59        = 12'h3EB,
    CSR_PMPADDR60        = 12'h3EC,
    CSR_PMPADDR61        = 12'h3ED,
    CSR_PMPADDR62        = 12'h3EE,
    CSR_PMPADDR63        = 12'h3EF,
    CSR_MVENDORID        = 12'hF11,
    CSR_MARCHID          = 12'hF12,
    CSR_MIMPID           = 12'hF13,
    CSR_MHARTID          = 12'hF14,
    CSR_MCONFIGPTR       = 12'hF15,
    CSR_MCYCLE           = 12'hB00,
    CSR_MCYCLEH          = 12'hB80,
    CSR_MINSTRET         = 12'hB02,
    CSR_MINSTRETH        = 12'hB82,
    //Performance Counters
    CSR_MHPM_COUNTER_3   = 12'hB03,
    CSR_MHPM_COUNTER_4   = 12'hB04,
    CSR_MHPM_COUNTER_5   = 12'hB05,
    CSR_MHPM_COUNTER_6   = 12'hB06,
    CSR_MHPM_COUNTER_7   = 12'hB07,
    CSR_MHPM_COUNTER_8   = 12'hB08,
    CSR_MHPM_COUNTER_9   = 12'hB09,  // reserved
    CSR_MHPM_COUNTER_10  = 12'hB0A,  // reserved
    CSR_MHPM_COUNTER_11  = 12'hB0B,  // reserved
    CSR_MHPM_COUNTER_12  = 12'hB0C,  // reserved
    CSR_MHPM_COUNTER_13  = 12'hB0D,  // reserved
    CSR_MHPM_COUNTER_14  = 12'hB0E,  // reserved
    CSR_MHPM_COUNTER_15  = 12'hB0F,  // reserved
    CSR_MHPM_COUNTER_16  = 12'hB10,  // reserved
    CSR_MHPM_COUNTER_17  = 12'hB11,  // reserved
    CSR_MHPM_COUNTER_18  = 12'hB12,  // reserved
    CSR_MHPM_COUNTER_19  = 12'hB13,  // reserved
    CSR_MHPM_COUNTER_20  = 12'hB14,  // reserved
    CSR_MHPM_COUNTER_21  = 12'hB15,  // reserved
    CSR_MHPM_COUNTER_22  = 12'hB16,  // reserved
    CSR_MHPM_COUNTER_23  = 12'hB17,  // reserved
    CSR_MHPM_COUNTER_24  = 12'hB18,  // reserved
    CSR_MHPM_COUNTER_25  = 12'hB19,  // reserved
    CSR_MHPM_COUNTER_26  = 12'hB1A,  // reserved
    CSR_MHPM_COUNTER_27  = 12'hB1B,  // reserved
    CSR_MHPM_COUNTER_28  = 12'hB1C,  // reserved
    CSR_MHPM_COUNTER_29  = 12'hB1D,  // reserved
    CSR_MHPM_COUNTER_30  = 12'hB1E,  // reserved
    CSR_MHPM_COUNTER_31  = 12'hB1F,  // reserved
    CSR_MHPM_COUNTER_3H  = 12'hB83,
    CSR_MHPM_COUNTER_4H  = 12'hB84,
    CSR_MHPM_COUNTER_5H  = 12'hB85,
    CSR_MHPM_COUNTER_6H  = 12'hB86,
    CSR_MHPM_COUNTER_7H  = 12'hB87,
    CSR_MHPM_COUNTER_8H  = 12'hB88,
    CSR_MHPM_COUNTER_9H  = 12'hB89,  // reserved
    CSR_MHPM_COUNTER_10H = 12'hB8A,  // reserved
    CSR_MHPM_COUNTER_11H = 12'hB8B,  // reserved
    CSR_MHPM_COUNTER_12H = 12'hB8C,  // reserved
    CSR_MHPM_COUNTER_13H = 12'hB8D,  // reserved
    CSR_MHPM_COUNTER_14H = 12'hB8E,  // reserved
    CSR_MHPM_COUNTER_15H = 12'hB8F,  // reserved
    CSR_MHPM_COUNTER_16H = 12'hB90,  // reserved
    CSR_MHPM_COUNTER_17H = 12'hB91,  // reserved
    CSR_MHPM_COUNTER_18H = 12'hB92,  // reserved
    CSR_MHPM_COUNTER_19H = 12'hB93,  // reserved
    CSR_MHPM_COUNTER_20H = 12'hB94,  // reserved
    CSR_MHPM_COUNTER_21H = 12'hB95,  // reserved
    CSR_MHPM_COUNTER_22H = 12'hB96,  // reserved
    CSR_MHPM_COUNTER_23H = 12'hB97,  // reserved
    CSR_MHPM_COUNTER_24H = 12'hB98,  // reserved
    CSR_MHPM_COUNTER_25H = 12'hB99,  // reserved
    CSR_MHPM_COUNTER_26H = 12'hB9A,  // reserved
    CSR_MHPM_COUNTER_27H = 12'hB9B,  // reserved
    CSR_MHPM_COUNTER_28H = 12'hB9C,  // reserved
    CSR_MHPM_COUNTER_29H = 12'hB9D,  // reserved
    CSR_MHPM_COUNTER_30H = 12'hB9E,  // reserved
    CSR_MHPM_COUNTER_31H = 12'hB9F,  // reserved
    // Cache Control (platform specifc)
    CSR_DCACHE           = 12'h7C1,
    CSR_ICACHE           = 12'h7C0,
    // Accelerator memory consistency (platform specific)
    CSR_ACC_CONS         = 12'h7C2,
    // Triggers
    CSR_TSELECT          = 12'h7A0,
    CSR_TDATA1           = 12'h7A1,
    CSR_TDATA2           = 12'h7A2,
    CSR_TDATA3           = 12'h7A3,
    CSR_TINFO            = 12'h7A4,
    // Debug CSR
    CSR_DCSR             = 12'h7b0,
    CSR_DPC              = 12'h7b1,
    CSR_DSCRATCH0        = 12'h7b2,  // optional
    CSR_DSCRATCH1        = 12'h7b3,  // optional
    // Counters and Timers from Zicntr extension (User Mode - R/O Shadows)
    CSR_CYCLE            = 12'hC00,
    CSR_CYCLEH           = 12'hC80,
    CSR_TIME             = 12'hC01,
    CSR_TIMEH            = 12'hC81,
    CSR_INSTRET          = 12'hC02,
    CSR_INSTRETH         = 12'hC82,
    // Performance counters from Zihpm extension (User Mode - R/O Shadows)
    CSR_HPM_COUNTER_3    = 12'hC03,
    CSR_HPM_COUNTER_4    = 12'hC04,
    CSR_HPM_COUNTER_5    = 12'hC05,
    CSR_HPM_COUNTER_6    = 12'hC06,
    CSR_HPM_COUNTER_7    = 12'hC07,
    CSR_HPM_COUNTER_8    = 12'hC08,
    CSR_HPM_COUNTER_9    = 12'hC09,  // reserved
    CSR_HPM_COUNTER_10   = 12'hC0A,  // reserved
    CSR_HPM_COUNTER_11   = 12'hC0B,  // reserved
    CSR_HPM_COUNTER_12   = 12'hC0C,  // reserved
    CSR_HPM_COUNTER_13   = 12'hC0D,  // reserved
    CSR_HPM_COUNTER_14   = 12'hC0E,  // reserved
    CSR_HPM_COUNTER_15   = 12'hC0F,  // reserved
    CSR_HPM_COUNTER_16   = 12'hC10,  // reserved
    CSR_HPM_COUNTER_17   = 12'hC11,  // reserved
    CSR_HPM_COUNTER_18   = 12'hC12,  // reserved
    CSR_HPM_COUNTER_19   = 12'hC13,  // reserved
    CSR_HPM_COUNTER_20   = 12'hC14,  // reserved
    CSR_HPM_COUNTER_21   = 12'hC15,  // reserved
    CSR_HPM_COUNTER_22   = 12'hC16,  // reserved
    CSR_HPM_COUNTER_23   = 12'hC17,  // reserved
    CSR_HPM_COUNTER_24   = 12'hC18,  // reserved
    CSR_HPM_COUNTER_25   = 12'hC19,  // reserved
    CSR_HPM_COUNTER_26   = 12'hC1A,  // reserved
    CSR_HPM_COUNTER_27   = 12'hC1B,  // reserved
    CSR_HPM_COUNTER_28   = 12'hC1C,  // reserved
    CSR_HPM_COUNTER_29   = 12'hC1D,  // reserved
    CSR_HPM_COUNTER_30   = 12'hC1E,  // reserved
    CSR_HPM_COUNTER_31   = 12'hC1F,  // reserved
    CSR_HPM_COUNTER_3H   = 12'hC83,
    CSR_HPM_COUNTER_4H   = 12'hC84,
    CSR_HPM_COUNTER_5H   = 12'hC85,
    CSR_HPM_COUNTER_6H   = 12'hC86,
    CSR_HPM_COUNTER_7H   = 12'hC87,
    CSR_HPM_COUNTER_8H   = 12'hC88,
    CSR_HPM_COUNTER_9H   = 12'hC89,  // reserved
    CSR_HPM_COUNTER_10H  = 12'hC8A,  // reserved
    CSR_HPM_COUNTER_11H  = 12'hC8B,  // reserved
    CSR_HPM_COUNTER_12H  = 12'hC8C,  // reserved
    CSR_HPM_COUNTER_13H  = 12'hC8D,  // reserved
    CSR_HPM_COUNTER_14H  = 12'hC8E,  // reserved
    CSR_HPM_COUNTER_15H  = 12'hC8F,  // reserved
    CSR_HPM_COUNTER_16H  = 12'hC90,  // reserved
    CSR_HPM_COUNTER_17H  = 12'hC91,  // reserved
    CSR_HPM_COUNTER_18H  = 12'hC92,  // reserved
    CSR_HPM_COUNTER_19H  = 12'hC93,  // reserved
    CSR_HPM_COUNTER_20H  = 12'hC94,  // reserved
    CSR_HPM_COUNTER_21H  = 12'hC95,  // reserved
    CSR_HPM_COUNTER_22H  = 12'hC96,  // reserved
    CSR_HPM_COUNTER_23H  = 12'hC97,  // reserved
    CSR_HPM_COUNTER_24H  = 12'hC98,  // reserved
    CSR_HPM_COUNTER_25H  = 12'hC99,  // reserved
    CSR_HPM_COUNTER_26H  = 12'hC9A,  // reserved
    CSR_HPM_COUNTER_27H  = 12'hC9B,  // reserved
    CSR_HPM_COUNTER_28H  = 12'hC9C,  // reserved
    CSR_HPM_COUNTER_29H  = 12'hC9D,  // reserved
    CSR_HPM_COUNTER_30H  = 12'hC9E,  // reserved
    CSR_HPM_COUNTER_31H  = 12'hC9F   // reserved
  } csr_reg_t;

  localparam logic [63:0] SSTATUS_UIE = 'h00000001;
  localparam logic [63:0] SSTATUS_SIE = 'h00000002;
  localparam logic [63:0] SSTATUS_SPIE = 'h00000020;
  localparam logic [63:0] SSTATUS_SPP = 'h00000100;
  localparam logic [63:0] SSTATUS_FS = 'h00006000;
  localparam logic [63:0] SSTATUS_XS = 'h00018000;
  localparam logic [63:0] SSTATUS_SUM = 'h00040000;
  localparam logic [63:0] SSTATUS_MXR = 'h00080000;
  localparam logic [63:0] SSTATUS_UPIE = 'h00000010;
  localparam logic [63:0] SSTATUS_UXL = 64'h0000000300000000;
  function automatic logic [63:0] sstatus_sd(logic IS_XLEN64);
    return {IS_XLEN64, 31'h00000000, ~IS_XLEN64, 31'h00000000};
  endfunction

  localparam logic [63:0] HSTATUS_VSBE = 'h00000020;
  localparam logic [63:0] HSTATUS_GVA = 'h00000040;
  localparam logic [63:0] HSTATUS_SPV = 'h00000080;
  localparam logic [63:0] HSTATUS_SPVP = 'h00000100;
  localparam logic [63:0] HSTATUS_HU = 'h00000200;
  localparam logic [63:0] HSTATUS_VGEIN = 'h0003F000;
  localparam logic [63:0] HSTATUS_VTVM = 'h00100000;
  localparam logic [63:0] HSTATUS_VTW = 'h00200000;
  localparam logic [63:0] HSTATUS_VTSR = 'h00400000;
  localparam logic [63:0] HSTATUS_VSXL = 64'h0000000300000000;

  localparam logic [63:0] MSTATUS_UIE = 'h00000001;
  localparam logic [63:0] MSTATUS_SIE = 'h00000002;
  localparam logic [63:0] MSTATUS_HIE = 'h00000004;
  localparam logic [63:0] MSTATUS_MIE = 'h00000008;
  localparam logic [63:0] MSTATUS_UPIE = 'h00000010;
  localparam logic [63:0] MSTATUS_SPIE = 'h00000020;
  localparam logic [63:0] MSTATUS_HPIE = 'h00000040;
  localparam logic [63:0] MSTATUS_MPIE = 'h00000080;
  localparam logic [63:0] MSTATUS_SPP = 'h00000100;
  localparam logic [63:0] MSTATUS_HPP = 'h00000600;
  localparam logic [63:0] MSTATUS_MPP = 'h00001800;
  localparam logic [63:0] MSTATUS_FS = 'h00006000;
  localparam logic [63:0] MSTATUS_XS = 'h00018000;
  localparam logic [63:0] MSTATUS_MPRV = 'h00020000;
  localparam logic [63:0] MSTATUS_SUM = 'h00040000;
  localparam logic [63:0] MSTATUS_MXR = 'h00080000;
  localparam logic [63:0] MSTATUS_TVM = 'h00100000;
  localparam logic [63:0] MSTATUS_TW = 'h00200000;
  localparam logic [63:0] MSTATUS_TSR = 'h00400000;
  function automatic logic [63:0] mstatus_uxl(logic IS_XLEN64);
    return {30'h0000000, IS_XLEN64, IS_XLEN64, 32'h00000000};
  endfunction
  function automatic logic [63:0] mstatus_sxl(logic IS_XLEN64);
    return {28'h0000000, IS_XLEN64, IS_XLEN64, 34'h00000000};
  endfunction
  function automatic logic [63:0] mstatus_sd(logic IS_XLEN64);
    return {IS_XLEN64, 31'h00000000, ~IS_XLEN64, 31'h00000000};
  endfunction

  localparam logic [63:0] MENVCFG_FIOM = 'h00000001;
  localparam logic [63:0] MENVCFG_CBIE = 'h00000030;
  localparam logic [63:0] MENVCFG_CBFE = 'h00000040;
  localparam logic [63:0] MENVCFG_CBZE = 'h00000080;
  localparam logic [63:0] MENVCFG_PBMTE = 64'h4000000000000000;
  localparam logic [63:0] MENVCFG_STCE = 64'h8000000000000000;



  typedef enum logic [2:0] {
    CSRRW  = 3'h1,
    CSRRS  = 3'h2,
    CSRRC  = 3'h3,
    CSRRWI = 3'h5,
    CSRRSI = 3'h6,
    CSRRCI = 3'h7
  } csr_op_t;

  // decoded CSR address
  typedef struct packed {
    logic [1:0] rw;
    priv_lvl_t  priv_lvl;
    logic [7:0] address;
  } csr_addr_t;

  typedef union packed {
    csr_reg_t  address;
    csr_addr_t csr_decode;
  } csr_t;

  // Floating-Point control and status register (32-bit!)
  typedef struct packed {
    logic [31:15] reserved;  // reserved for L extension, return 0 otherwise
    logic [6:0]   fprec;     // div/sqrt precision control
    logic [2:0]   frm;       // float rounding mode
    logic [4:0]   fflags;    // float exception flags
  } fcsr_t;

  // PMP
  typedef enum logic [1:0] {
    OFF   = 2'b00,
    TOR   = 2'b01,
    NA4   = 2'b10,
    NAPOT = 2'b11
  } pmp_addr_mode_t;

  // PMP Access Type
  typedef enum logic [2:0] {
    ACCESS_NONE  = 3'b000,
    ACCESS_READ  = 3'b001,
    ACCESS_WRITE = 3'b010,
    ACCESS_EXEC  = 3'b100
  } pmp_access_t;

  typedef struct packed {
    logic x;
    logic w;
    logic r;
  } pmpcfg_access_t;

  // packed struct of a PMP configuration register (8bit)
  typedef struct packed {
    logic           locked;       // lock this configuration
    logic [1:0]     reserved;
    pmp_addr_mode_t addr_mode;    // Off, TOR, NA4, NAPOT
    pmpcfg_access_t access_type;
  } pmpcfg_t;

  // -----
  // SPMP
  // -----
  // SPMP configuration register
  typedef struct packed {
      logic            s_mode;        // S-mode /U-mode rule
      logic [1:0]      reserved;
      pmp_addr_mode_t  addr_mode;     // Off, TOR, NA4, NAPOT
      pmpcfg_access_t  access_perm;   // [x, w r]
  } spmpcfg_t;

  // -----
  // Debug
  // -----
  typedef struct packed {
    logic [31:28] xdebugver;
    logic [27:18] zero2;
    logic         ebreakvs;
    logic         ebreakvu;
    logic         ebreakm;
    logic         zero1;
    logic         ebreaks;
    logic         ebreaku;
    logic         stepie;
    logic         stopcount;
    logic         stoptime;
    logic [8:6]   cause;
    logic         v;
    logic         mprven;
    logic         nmip;
    logic         step;
    priv_lvl_t    prv;
  } dcsr_t;

  // Instruction Generation *incomplete*
  function automatic logic [31:0] jal(logic [4:0] rd, logic [20:0] imm);
    // OpCode Jal
    return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h6f};
  endfunction

  function automatic logic [31:0] jalr(logic [4:0] rd, logic [4:0] rs1, logic [11:0] offset);
    // OpCode Jal
    return {offset[11:0], rs1, 3'b0, rd, 7'h67};
  endfunction

  function automatic logic [31:0] andi(logic [4:0] rd, logic [4:0] rs1, logic [11:0] imm);
    // OpCode andi
    return {imm[11:0], rs1, 3'h7, rd, 7'h13};
  endfunction

  function automatic logic [31:0] slli(logic [4:0] rd, logic [4:0] rs1, logic [5:0] shamt);
    // OpCode slli
    return {6'b0, shamt[5:0], rs1, 3'h1, rd, 7'h13};
  endfunction

  function automatic logic [31:0] srli(logic [4:0] rd, logic [4:0] rs1, logic [5:0] shamt);
    // OpCode srli
    return {6'b0, shamt[5:0], rs1, 3'h5, rd, 7'h13};
  endfunction

  function automatic logic [31:0] load(logic [2:0] size, logic [4:0] dest, logic [4:0] base,
                                       logic [11:0] offset);
    // OpCode Load
    return {offset[11:0], base, size, dest, 7'h03};
  endfunction

  function automatic logic [31:0] auipc(logic [4:0] rd, logic [20:0] imm);
    // OpCode Auipc
    return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h17};
  endfunction

  function automatic logic [31:0] store(logic [2:0] size, logic [4:0] src, logic [4:0] base,
                                        logic [11:0] offset);
    // OpCode Store
    return {offset[11:5], src, base, size, offset[4:0], 7'h23};
  endfunction

  function automatic logic [31:0] float_load(logic [2:0] size, logic [4:0] dest, logic [4:0] base,
                                             logic [11:0] offset);
    // OpCode Load
    return {offset[11:0], base, size, dest, 7'b00_001_11};
  endfunction

  function automatic logic [31:0] float_store(logic [2:0] size, logic [4:0] src, logic [4:0] base,
                                              logic [11:0] offset);
    // OpCode Store
    return {offset[11:5], src, base, size, offset[4:0], 7'b01_001_11};
  endfunction

  function automatic logic [31:0] csrw(csr_reg_t csr, logic [4:0] rs1);
    // CSRRW, rd, OpCode System
    return {csr, rs1, 3'h1, 5'h0, 7'h73};
  endfunction

  function automatic logic [31:0] csrr(csr_reg_t csr, logic [4:0] dest);
    // rs1, CSRRS, rd, OpCode System
    return {csr, 5'h0, 3'h2, dest, 7'h73};
  endfunction

  function automatic logic [31:0] branch(logic [4:0] src2, logic [4:0] src1, logic [2:0] funct3,
                                         logic [11:0] offset);
    // OpCode Branch
    return {offset[11], offset[9:4], src2, src1, funct3, offset[3:0], offset[10], 7'b11_000_11};
  endfunction

  function automatic logic [31:0] ebreak();
    return 32'h00100073;
  endfunction

  function automatic logic [31:0] wfi();
    return 32'h10500073;
  endfunction

  function automatic logic [31:0] nop();
    return 32'h00000013;
  endfunction

  function automatic logic [31:0] illegal();
    return 32'h00000000;
  endfunction

  // This functions converts S-mode CSR addresses into VS-mode CSR addresses
  // when V=1 (i.e., running in VS-mode).
  function automatic csr_t convert_vs_access_csr(csr_t csr_addr, logic v);
    csr_t ret;
    ret = csr_addr;
    unique case (csr_addr.address) inside
      [CSR_SSTATUS : CSR_STVEC], [CSR_SSCRATCH : CSR_SATP], [CSR_SPMPCFG0 : CSR_SPMPSWITCH1]: begin
        if (v) begin
          ret.csr_decode.priv_lvl = PRIV_LVL_HS;
        end
        return ret;
      end
      default: return ret;
    endcase
  endfunction


  // trace log compatible to spikes commit log feature
  // pragma translate_off
  function string spikeCommitLog(logic [63:0] pc, priv_lvl_t priv_lvl, logic [31:0] instr,
                                 logic [4:0] rd, logic [63:0] result, logic rd_fpr);
    string rd_s;
    string instr_word;

    automatic string rf_s = rd_fpr ? "f" : "x";

    if (instr[1:0] != 2'b11) begin
      instr_word = $sformatf("(0x%h)", instr[15:0]);
    end else begin
      instr_word = $sformatf("(0x%h)", instr);
    end

    if (rd < 10) rd_s = $sformatf("%s %0d", rf_s, rd);
    else rd_s = $sformatf("%s%0d", rf_s, rd);

    if (rd_fpr || rd != 0) begin
      // 0 0x0000000080000118 (0xeecf8f93) x31 0x0000000080004000
      return $sformatf("%d 0x%h %s %s 0x%h\n", priv_lvl, pc, instr_word, rd_s, result);
    end else begin
      // 0 0x000000008000019c (0x0040006f)
      return $sformatf("%d 0x%h %s\n", priv_lvl, pc, instr_word);
    end
  endfunction

  typedef struct {
    byte priv;
    longint unsigned pc;
    byte is_fp;
    byte rd;
    longint unsigned data;
    int unsigned instr;
    byte was_exception;
  } commit_log_t;
  // pragma translate_on

endpackage
