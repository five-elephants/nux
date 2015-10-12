// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


package Pu_inst;
	//import Pu_types::*;

	/* Definition of instruction opcodes */
	typedef enum logic[5:0] {
		Op_null        = 0,
		Op_twi         = 3,
		Op_nve_xo      = 4,
		Op_nvecmpi     = 5,
		Op_syncmpi     = 6,
		Op_mulli       = 7,
		Op_subfic      = 8,
		Op_syncmpi_rec = 9,
		Op_cmpli       = 10,
		Op_cmpi        = 11,
		Op_addic       = 12,
		Op_addic_rec   = 13,
		Op_addi        = 14,
		Op_addis       = 15,
		Op_bc          = 16,
		Op_branch      = 18,
		Op_bclr        = 19,
		Op_rlwimi      = 20,
		Op_rlwinm      = 21,
		Op_rlwnm       = 23,
		Op_ori         = 24,
		Op_oris        = 25,
		Op_xori        = 26,
		Op_xoris       = 27,
		Op_andi        = 28,
		Op_andis       = 29,
		Op_alu_xo      = 31,
		Op_lwz         = 32,
		Op_lwzu        = 33,
		Op_lbz         = 34,
		Op_lbzu        = 35,
		Op_stw         = 36,
		Op_stwu        = 37,
		Op_stb         = 38,
		Op_stbu        = 39,
		Op_lhz         = 40,
		Op_lhzu        = 41,
		Op_lha         = 42,
		Op_lhau        = 43,
		Op_sth         = 44,
		Op_sthu        = 45,
		Op_lmw         = 46,
		Op_stmw        = 47
	} Opcd;

	typedef enum logic[9:0] {
		Xop_cmp     =   0,
		Xop_tw      =   4,
		Xop_lwzx    =  23,
		Xop_slw     =  24,
		Xop_cntlzw  =  26,
		Xop_and     =  28,
		Xop_cmpl    =  32,
		Xop_nvem    =  48,
		Xop_nves    =  49,
		Xop_nvemtl  =  50,
		Xop_lwzux   =  55,
		Xop_andc    =  60,
		Xop_wait    =  62,
		Xop_mfmsr   =  83,
		Xop_lbzx    =  87,
		Xop_lbzux   = 119,
		Xop_popcb   = 122,
		Xop_nor     = 124,
		Xop_mtmsr   = 146,
		Xop_stwx    = 151,
		Xop_prtyw   = 154,
		Xop_stwux   = 183,
		Xop_stbx    = 215,
		Xop_stbux   = 247,
		Xop_lhzx    = 279,
		Xop_eqv     = 284,
		Xop_eciwx   = 310,
		Xop_lhzux   = 311,
		Xop_xor     = 316,
		//Xop_popcw   = 378,
		Xop_lhax    = 343,
		Xop_lhaux   = 375,
		Xop_sthx    = 407,
		Xop_orc     = 412,
		Xop_ecowx   = 438,
		Xop_sthux   = 439,
		Xop_or      = 444,
		Xop_nand    = 476,
		Xop_srw     = 536,
		Xop_sync    = 598,

		Xop_synm    = 648,
		Xop_syns    = 649,
		Xop_synmtl  = 650,
		Xop_synmtvr = 651,
		Xop_synmfvr = 652,
		Xop_synmtp  = 653,
		Xop_synmfp  = 654,
		Xop_synmvvr = 655,
		Xop_synops  = 656,
		Xop_synswp  = 657,

		//Xop_fxvmahm = 664,  // fixed-vector-multiply-accumulate-halfword-modulo
		//Xop_fxvlax  = 665,  // fixed-vector-load-array-indexed
		//Xop_fxvstax = 666,  // fixed-vector-store-array-indexed
		//Xop_fxvcmph = 667,  // fixed-vector-compare-halfword

		Xop_sraw    = 792,
		Xop_srawi   = 824,
		Xop_extsh   = 922,
		Xop_extsb   = 954
	} X_opcd;

	typedef enum logic[8:0] {
		Xop_xo_null=   0,  // needed for synthesis
		Xop_subfc  =   8,
		Xop_addc   =  10,
		Xop_mulhwu =  11,
		Xop_subf   =  40,
		Xop_mulhw  =  75,
		Xop_neg    = 104,
		Xop_subfe  = 136,
		Xop_adde   = 138,
		Xop_subfze = 200,
		Xop_addze  = 202,
		Xop_subfme = 232,
		Xop_addme  = 234,
		Xop_mullw  = 235,
		Xop_add    = 266,
		Xop_divwu  = 459,
		Xop_divw   = 491
	} Xo_opcd;

	typedef enum logic[9:0] {
		Xxop_mcrf   =   0,
		Xxop_bclr   =  16,
		Xxop_crnor  =  33,
		Xxop_rfmci  =  38,
		Xxop_rfi    =  50,
		Xxop_rfci   =  51,
		Xxop_crandc = 129,
		Xxop_crxor  = 193,
		Xxop_crnand = 225,
		Xxop_creqv  = 289,
		Xxop_crand  = 257,
		Xxop_crorc  = 417,
		Xxop_cror   = 449,
		Xxop_bcctr  = 528
	} Xl_opcd;

	typedef enum logic[9:0] {
		Xop_xfx_null=   0,  // needed for synthesis
		Xop_mfocrf  =  19,
		Xop_mtocrf  = 144,
		Xop_mfspr   = 339,
		Xop_mtspr   = 467
	} Xfx_opcd;

	/** Extended opcodes for fixed-point vector extension
	 *
	 * Used in combination with primary opcode 4 (Op_nve_xo). */
	typedef enum logic[8:0] {
		Xop_fxv_null      =   0,
		Xop_fxvmahm       =  12, // 332,  // fixed-vector-multiply-accumulate-halfword-modulo
		Xop_fxvmabm       =  13,          // fixed-vector-multiply-accumulate-byte-modulo
		Xop_fxvmtacb      =  14,          // fixed-vector-move-to-accumulator-byte
		Xop_fxvmtach      =  15,          // fixed-vector-move-to-accumulator-halfword
		Xop_fxvmahfs      =  28,          // fixed-vector-multiply-accumulate-halfword-fractional-saturating
		Xop_fxvmabfs      =  29,          // fixed-vector-multiply-accumulate-byte-fractional-saturating
		Xop_fxvmtacbf     =  30,          // fixed-vector-move-to-accumulator-byte-fractional
		Xop_fxvmtachf     =  31,          // fixed-vector-move-to-accumulator-halfword-fractional
		Xop_fxvmatachm    =  44,          // fixed-vector-multiply-accumulate-to-accumulator-halfword-modulo
		Xop_fxvmatacbm    =  45,          // fixed-vector-multiply-accumulate-save-to-accumulator-byte-modulo
		Xop_fxvmatachfs   =  60,          // fixed-vector-multiply-accumulate-and-save-to-accumulator-halfword-fractional-saturating
		Xop_fxvmatacbfs   =  61,          // fixed-vector-multiply-accumulate-and-save-to-accumulator-byte-fractional-saturating
		Xop_fxvmulhm      =  76,          // fixed-vector-multiply-halfword-modulo
		Xop_fxvmulbm      =  77,          // fixed-vector-multiply-byte-modulo
		Xop_fxvmulhfs     =  92,          // fixed-vector-multiply-halfword-fractional-saturating
		Xop_fxvmulbfs     =  93,          // fixed-vector-multiply-byte-fractional-saturating
		Xop_fxvmultachm   = 108,          // fixed-vector-multiply-save-to-accumulator-halfword-modulo
		Xop_fxvmultacbm   = 109,          // fixed-vector-multiply-save-to-accumulator-byte-modulo
		Xop_fxvmultachfs  = 124,          // fixed-vector-multiply-save-to-accumulator-halfword-fractional-saturating
		Xop_fxvmultacbfs  = 125,          // fixed-vector-multiply-save-to-accumulator-byte-fractional-saturating
		Xop_fxvinx        = 236,          // fixed-vector-in-indexed
		Xop_fxvpckbu      = 239,          // fixed-vector-pack-byte-upper
		Xop_fxvoutx       = 252,          // fixed-vector-out-indexed
		Xop_fxvpckbl      = 255,          // fixed-vector-pack-byte-lower
		Xop_fxvsplath     = 268,          // fixed-vector-splat-halfword
		Xop_fxvsplatb     = 269,          // fixed-vector-splat-byte
		Xop_fxvupckbr     = 271,          // fixed-vector-unpack-byte-right
		Xop_fxvupckbl     = 287,          // fixed-vector-unpack-byte-left
		Xop_fxvcmph       = 300,          // fixed-vector-compare-halfword
		Xop_fxvcmpb       = 301,          // fixed-vector-compare-byte
		Xop_fxvshh        = 316,          // fixed-vector-shift-halfword
		Xop_fxvshb        = 317,          // fixed-vector-shift-byte
		Xop_fxvsel        = 319,          // fixed-vector-select
		Xop_fxvsubhm      = 332,          // fixed-vector-subtract-halfword-modulo
		Xop_fxvsubbm      = 333,          // fixed-vector-subtract-byte-modulo
		Xop_fxvsubhfs     = 348,          // fixed-vector-subtract-halfword-fractional-saturating
		Xop_fxvsubbfs     = 349,          // fixed-vector-subtract-byte-fractional-saturating
		// TODO addactachm: the modulo is superfluous
		Xop_fxvaddactachm = 364,          // fixed-vector-add-accumulator-save-to-accumulator-halfword-modulo
		Xop_fxvaddactacb  = 365,          // fixed-vector-add-accumulator-save-to-accumulator-byte
		// TODO is this not saturating?
		Xop_fxvaddactachf = 380,          // fixed-vector-add-accumulator-save-to-accumulator-halfword-fractional
		Xop_fxvaddactacbf = 381,          // fixed-vector-add-accumulator-save-to-accumulator-byte-fractional
		// TODO addtachm: the modulo is superfluous
		Xop_fxvaddachm    = 396,          // fixed-vector-add-accumulator-halfword-modulo
		Xop_fxvaddacbm    = 397,          // fixed-vector-add-accumulator-byte-modulo
		Xop_fxvaddachfs   = 412,          // fixed-vector-add-accumulator-halfword-fractional-saturating
		Xop_fxvaddacbfs   = 413,          // fixed-vector-add-accumulator-byte-fractional-saturating
		Xop_fxvaddtachm   = 428,          // fixed-vector-add-and-save-to-accumulator-halfword-modulo
		Xop_fxvaddtacb    = 429,          // fixed-vector-add-and-save-to-accumulator-byte-modulo
		Xop_fxvaddhm      = 460,          // fixed-vector-add-halfword-modulo
		Xop_fxvaddbm      = 461,          // fixed-vector-add-byte-modulo
		Xop_fxvaddhfs     = 476,          // fixed-vector-add-halfword-fractional-saturating
		Xop_fxvaddbfs     = 477,          // fixed-vector-add-byte-fractional-saturating
		Xop_fxvlax        = 492, // 333,  // fixed-vector-load-array-indexed
		Xop_fxvstax       = 508  // 334,  // fixed-vector-store-array-indexed
	} Fxv_opcd;

	typedef enum logic[1:0] {
		Fxv_cond_null = 2'b00,
		Fxv_cond_gt   = 2'b01,
		Fxv_cond_lt   = 2'b10,
		Fxv_cond_eq   = 2'b11
	} Fxv_cond;

	/* Definition of instruction formats */
	typedef struct packed {
		Opcd opcd;
		logic[23:0] li;
		logic aa;
		logic lk;
	} Inst_i;

	typedef struct packed {
		Opcd opcd;
		logic[4:0] bo;
		logic[4:0] bi;
		logic[13:0] bd;
		logic aa;
		logic lk;
	} Inst_b;

	typedef struct packed {
		Opcd opcd;
		logic[4:0] rt;
		logic[4:0] ra;
		logic[15:0] d;
	} Inst_d;

	typedef struct packed {
		Opcd opcd;
		logic[4:0] rt;
		logic[4:0] ra;
		logic[4:0] rb;
		logic oe;
		Xo_opcd xo;
		logic rc;
	} Inst_xo;

	typedef struct packed {
		Opcd opcd;
		logic[4:0] rt;
		logic[4:0] ra;
		logic[4:0] rb;
		X_opcd xo;
		logic rc;
	} Inst_x;

	typedef struct packed {
		Opcd opcd;
		logic[4:0] rs;
		logic[4:0] ra;
		logic[4:0] rb;
		logic[4:0] mb;
		logic[4:0] me;
		logic rc;
	} Inst_m;

	typedef struct packed {
		Opcd opcd;
		logic[4:0] rt;
		logic[9:0] spr;
		Xfx_opcd xo;
		logic not_used;
	} Inst_xfx;

	typedef struct packed {
		Opcd opcd;
		logic[4:0] bt;
		logic[4:0] ba;
		logic[4:0] bb;
		Xl_opcd    xo;
		logic      lk;
	} Inst_xl;

	typedef struct packed {
		Opcd opcd;
		logic[4:0] rt;
		logic[4:0] ra;
		logic[4:0] rb;
		Fxv_opcd xo;
		Fxv_cond cond;
	} Inst_fxv;


	typedef union packed {
		Inst_i i;
		Inst_b b;
		Inst_d d;
		Inst_xo xo;
		Inst_x x;
		Inst_m m;
		Inst_xfx xfx;
		Inst_xl xl;
		Inst_fxv fxv;
	} Inst;

	localparam Inst INST_NOP = Inst'({Op_ori, 26'b0});
	localparam Inst INST_WAIT = Inst'({32'h7c_00_00_7c});

endpackage

/* vim: set noet fenc= ff=unix sts=0 sw=4 ts=4 : */
