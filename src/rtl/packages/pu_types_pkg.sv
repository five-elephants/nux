// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


package Pu_types;
	localparam int DWIDTH = 32;	
    localparam int LOAD_STORE_CYCLES = 0;
	localparam int NUM_NVE_LUT = 2;

	typedef logic [DWIDTH-1:0] Word;
	typedef logic [DWIDTH:0] Word_c;  // Word with carry
	typedef logic [4:0] Reg_index;
	typedef logic [DWIDTH-1:0] Address;
    typedef logic [3:0] Ls_cycle_counter;
    typedef logic [63:0] Time_base;
    typedef logic [31:0] Timer;
	typedef logic [7:0] Nve_sstate;
	typedef logic [0:15][3:0] Nve_lut;

	/*typedef enum logic [3:0] {  // XXX count leading zeros is missing
		//Alu_nop = 'h0,
		
		// arithmetic operations
		Alu_add = 'h1,
		Alu_sub = 'h2,
		Alu_neg = 'h3,
		
		// logic operations
		Alu_and = 'h4,
		Alu_andc = 'h0,
		Alu_or  = 'h5,
		Alu_orc = 'hf,
		Alu_xor = 'h6,
		Alu_nand = 'h7,
		Alu_nor = 'h8,
		Alu_eqv = 'h9,
		Alu_esh = 'ha,
		Alu_esb = 'hb,
		Alu_popcnt = 'hc,
		Alu_prty = 'hd,

		// shift/rotate operations
		Alu_rotl = 'he
	} Alu_op;*/

	typedef enum logic[5:0] {
		// Adder ops
		Alu_add    = 6'b000000,
		Alu_sub    = 6'b000001,
		Alu_neg    = 6'b000010,
		Alu_cmp    = 6'b000101,
		Alu_cmpl   = 6'b000111,

		// Condition register logical ops
		//Alu_crand  = 6'b001000,
		//Alu_crandc = 6'b001001,
		//Alu_cror   = 6'b001010,
		//Alu_crorc  = 6'b001011,
		//Alu_crnand = 6'b001100,
		//Alu_crxor  = 6'b001101,
		//Alu_crnor  = 6'b001110,
		//Alu_creqv  = 6'b001111,

		// Logical ops
		Alu_and    = 6'b010000,
		Alu_andc   = 6'b010001,
		Alu_or     = 6'b010010,
		Alu_orc    = 6'b010011,
		Alu_nand   = 6'b010100,
		Alu_xor    = 6'b010101,
		Alu_nor    = 6'b010110,
		Alu_eqv    = 6'b010111,
		
		// Mul/div ops
		Alu_mul    = 6'b011000,  /**< multiply (return low word) */
		Alu_mulu   = 6'b011011,  /**< multiply unsigned (return high word) */
		Alu_mulh   = 6'b011010,  /**< multiply (return high word) */
		Alu_div    = 6'b011100,
		Alu_divu   = 6'b011101,

		Alu_cmpb   = 6'b110000,

		// Parity ops
		Alu_prty   = 6'b110001,

		// Population count ops
		Alu_popcnt = 6'b110010,

		// Rotate and mask ops
		Alu_rotl   = 6'b110011,

		// Integer select ops
		Alu_isel   = 6'b111000,
		Alu_esb    = 6'b111001,
		Alu_esh    = 6'b111010,

		// Leading zeros counting
		Alu_cntlz  = 6'b111111
	} Alu_op;

	/** Operations on condition register fields */
	typedef enum logic[2:0] {
		Cr_and  = 3'b000,
		Cr_andc = 3'b001,
		Cr_or   = 3'b010,
		Cr_orc  = 3'b011,
		Cr_nand = 3'b100,
		Cr_xor  = 3'b101,
		Cr_nor  = 3'b110,
		Cr_eqv  = 3'b111
	} Cr_op;

	typedef struct packed {
		logic lt;
		logic gt;
		logic eq;
		logic ov;
	} Cr_field;

	typedef struct packed {
		logic so;
		logic ov;
		logic ca;
	} Xer;

	typedef Cr_field [0:7] Condition_register;
	typedef logic[0:31] Cr_bits;

	/** Type for 32bit machine state register */
	typedef struct packed {
		logic        comp_mode;  // 0 - 32bit mode, 1 - 64bit mode
		logic[0:12]  reserved0;
		logic        ce;         // critical interrupts mask
		logic        reserved1;
		logic        ee;         // external interrupts mask
		logic        pr;         // 0 - privileged, 1 - problem state
		logic        fp;         // 1 - floating point available
		logic        me;         // machine check interrupts mask
		logic[0:1]   reserved2;
		logic        de;         // debug interrupts mask
		logic[0:2]   reserved3;
		logic        is;         // instructions address space
		logic        ds;         // data address space
		logic[0:3]   reserved4;
	} Msr;

	/** Type for the 32bit exception syndrome register */
	typedef struct packed {
		logic[0:3]   reserved0;
		logic        pil;  // program illegal instruction
		logic        ppr;  // program privileged instruction
		logic        ptr;  // program trap
		logic        fp;   // floating point
		logic        st;   // store operation
		logic        reserved1;
		logic[0:1]   dlk;  // implementation dependent
		logic        ap;   // auxiliary processor operation
		logic        puo;  // program unimplemented operation
		logic        bo;   // byte-ordering
		logic        pie;  // imprecise exception
		logic[0:4]   reserved2;
		logic        data; // data access
		logic        tlbi; // TLB ineligible
		logic        pt;   // page table
		logic        spv;  // signal processing operation
		logic        epid; // external process ID operation
		logic        vlemi;// VLE operation
		logic[0:2]   reserved3;
		logic        mif;  // missaligned instruction
		logic        reserved4;
	} Esr;

    /** Type for the 32bit timer control register */
    typedef struct packed {
        logic[0:1]   wp;   // watchdog timer period
        logic[0:1]   wrc;  // watchdog timer reset control
        logic        wie;  // watchdog timer interrupt enable
        logic        die;  // decrementer interrupt enable
        logic[0:1]   fp;   // fixed-interval timer period
        logic        fie;  // fixed-interval timer interrupt enable
        logic        are;  // auto-reload enable
        logic[21:0]  reserved;
    } Tcr;

    /** Type for the 32bit timer status register */
    typedef struct packed {
        logic        enw;  // enable next watchdog timer
        logic        wis;  // watchdog timer interrupt status
        logic[0:1]   wrs;  // watchdog timer reset status
        logic        dis;  // decrementer interrupt status
        logic        fis;  // fixed-interval timer interrupt status
        logic[25:0]  reserved;
    } Tsr;

	// TODO this is a hack!
	// bit position of bits within 32-bit XER register
	// should be replaced by consistent use of structs
	localparam int XER_CA = 29;

	typedef struct packed {
		logic  lts;  // less than signed
		logic  gts;  // greater than signed
		logic  eq;   // equal
		logic  ltu;  // less than unsigned
		logic  gtu;  // greater than unsigned
	} Trap_to;


	typedef enum logic[6:0] {
		Rmv_none = 7'b0000000,
		Rmv_gtc  = 7'b0000001,
		Rmv_ctg  = 7'b0000010,
		Rmv_stg  = 7'b0000100,
		Rmv_gts  = 7'b0001000,
		Rmv_ctc  = 7'b0010000,
		Rmv_gtm  = 7'b0100000,   // GPR to MSR
		Rmv_mtg  = 7'b1000000    // MSR to GPR
	} Register_move;

	typedef enum logic[0:3] {
		FREEZE_DC = 4'b1111,
		FREEZE_EX = 4'b0111,
		FREEZE_LS = 4'b0011,
		FREEZE_WB = 4'b0001
	} Freeze_at;


	/** Index encoding for special purpose registers */
	typedef enum logic[9:0] {
		Spr_null    = 10'b00000_00000,
		Spr_xer     = 10'b00001_00000,
		Spr_lnk     = 10'b01000_00000,
		Spr_ctr     = 10'b01001_00000,
		Spr_srr0    = 10'b11010_00000,
		Spr_srr1    = 10'b11011_00000,
		Spr_amr     = 10'b01101_00000,
        Spr_dec     = 10'b10110_00000,
        Spr_decar   = 10'b10110_00001,
		Spr_csrr0   = 10'b11010_00001,
		Spr_csrr1   = 10'b11011_00001,
		Spr_dear    = 10'b11101_00001,
		Spr_esr     = 10'b11110_00001,
		Spr_ctrl    = 10'b01000_00100,
		Spr_vrsave  = 10'b00000_01000,
		Spr_sprg3   = 10'b00011_01000,
		Spr_sprg4   = 10'b00100_01000,
		Spr_sprg5   = 10'b00101_01000,
		Spr_sprg6   = 10'b00110_01000,
		Spr_sprg7   = 10'b00111_01000,
        Spr_tsr     = 10'b10000_01010,
        Spr_tcr     = 10'b10100_01010,
		Spr_tbu     = 10'b11101_01000,
        Spr_tbl     = 10'b11100_01000,
		Spr_mcsrr0  = 10'b11010_10001,
		Spr_mcsrr1  = 10'b11011_10001,

		/* none PowerISA SPRs */
		Spr_gin     = 10'b00001_00010,
		Spr_gout    = 10'b00010_00010,
        Spr_goe     = 10'b00011_00010,
        Spr_iccr    = 10'b00100_00010
	} Spr_index;

	/** Type for a future reduction in size of the SPR index.
	*
	* Not all 2^10 possible SPRs exists. This type shall become a reduced
	* internal representation that may be used where space needs to be saved.
	* */
	typedef Spr_index Spr_reduced;

	typedef enum logic[2:0] {
		Load_null     = 3'b000,
		Load_byte     = 3'b001,
		Load_halfword = 3'b010,
		Load_word     = 3'b100
	} Load_mode;

	/** Enumeration of function units */
	typedef enum logic[4:0] {
		Fu_none   = 5'b00000,
		Fu_alu    = 5'b00001,
		Fu_rotm   = 5'b00010,
		Fu_spreu  = 5'b00100,
		Fu_mul    = 5'b01000,
		Fu_div    = 5'b10000
	} Func_unit;

	/** Enumeration of ports on functional units.
	* Used for example to control forwarding */
	typedef enum logic[7:0] {
		Fup_other  = 8'b00000000,
		Fup_alu_a  = 8'b00000001,
		Fup_alu_b  = 8'b00000010,
		Fup_rotm_x = 8'b00000100, 
		Fup_mul_a  = 8'b00001000,
		Fup_mul_b  = 8'b00010000,
		Fup_div_a  = 8'b00100000,
		Fup_div_b  = 8'b01000000,
		Fup_ls_din = 8'b10000000
	} Fu_port;

	/** Control signals for the bypass lines */
	typedef struct packed {
		logic fxdp_to_alu_a;
		logic fxdp_to_alu_b;
		logic fxdp_to_rotm_x;

		logic ls_to_alu_a;
		logic ls_to_alu_b;
	} Bypass_line_ctrl;

	

	/** This struct contains all control signals as they are generated
	* in the decode phase. (last counted as 126bit)*/
	typedef struct packed {
		logic          if_hold;
		logic          if_wait;
        logic          if_gpr_c_over;
        Reg_index      if_gpr_c;

		logic          alu_en;
		Alu_op         alu_op;
		logic[4:0]     alu_crl_ba;
		logic[4:0]     alu_crl_bb;
		logic[4:0]     alu_crl_bt;
		logic[4:0]     alu_isel_bc;
		logic          alu_isel_selb;
		logic          alu_multi_cycle;
		logic          alu_last_cycle;

		Cr_op          cr_op;

		Func_unit      fxdp_sel;
		logic          mul_high;
		logic          mul_unsigned;
		logic          div_unsigned;

		logic          branch_en;
		logic          br_jump;
		logic[4:0]     br_crbi;
		logic          br_cond;
		logic          br_mask_cond;
		logic          br_ctr_eq;
		logic          br_mask_ctr;
		logic          br_dec_ctr;
		logic          br_save_lnk;

		logic          trap_en;
		Trap_to        trap_to;

		logic          ls_en;
		logic          ls_we;
		Load_mode      ls_mode;
		logic          ls_multiple;
		logic          ls_first_cycle;
        logic          ls_multiple_inc;

		logic          wb_wr_cr;
		logic[7:0]     wb_record_cr;
		logic          wb_record_ca;
		logic          wb_record_ov;
		logic[7:0]     wb_src_cr;
		Register_move  wb_reg_mv;
		logic          wb_spr_we;
		logic[9:0]     wb_spr_sel;
		logic          wb_msr_we;
        logic          wb_sleep;

		logic          int_rest_base;
		logic          int_rest_crit;
		logic          int_rest_mcheck;
		logic          int_block_external;

		// asynchronous signals
		Reg_index      gpr_a;
		Reg_index      gpr_b;
		Reg_index      gpr_c;
		logic          read_gpr_a;
		logic          read_gpr_b;
		logic          read_gpr_c;
		logic          write_gpr_from_alu;
		logic          write_gpr_from_mem;
		Reg_index      gpr_from_alu;
		Reg_index      gpr_from_mem;
		logic          read_ctr;
		logic          write_ctr;
		logic          read_lnk;
		logic          write_lnk;
		logic[7:0]     write_cr;
		logic[7:0]     read_cr_0;
		logic[7:0]     read_cr_1;
		logic[7:0]     read_cr_2;
		logic          write_xer;
		logic          read_xer;
		logic          read_spr;
		logic          read_spr2;
		logic          write_spr;
		Spr_reduced    spr_src;
		Spr_reduced    spr_src2;
		Spr_reduced    spr_dest;
	} Control_word;



	typedef enum int {
		MEM_TIGHT = 0,
		MEM_BUS = 1
	} Opt_mem;

	function automatic logic[2:0] cr_idx_encode(input logic[7:0] sel);
		logic[2:0] rv;

		//unique case(sel)
		case(sel)
			8'b00000001: rv = 3'h0;
			8'b00000010: rv = 3'h1;
			8'b00000100: rv = 3'h2;
			8'b00001000: rv = 3'h3;
			8'b00010000: rv = 3'h4;
			8'b00100000: rv = 3'h5;
			8'b01000000: rv = 3'h6;
			8'b10000000: rv = 3'h7;
			default:     rv = 3'hx;
		endcase

		return rv;
	endfunction


	function automatic int clog2(input int x);
		int rv, y;
		y = 1;
		for(rv=0; y < x; rv++) begin 
			y = y * 2;
		end
		return rv;
		//return $clog2(x);
	endfunction

endpackage
