// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Pu_types::*;
import Pu_inst::*;
import Sit::*;

module Sit_mod
	#(	IMEM_ADDR_WIDTH = 10,
		DMEM_ADDR_WIDTH = 10 ); 

timeunit 1ns;
const time clk_period = 10ns;
logic clk;
logic reset;
logic pu_hold;
Word gout, gin, goe;

always begin
	#(clk_period/2) clk = 1;
	#(clk_period/2) clk = 0;
end

Pu_ctrl_if pu_ctrl_if();
Timer_if timer_if();

Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_if();
Ram_if #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_if();

Sim_memory #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem 
	(	.clk(clk),
		.reset(reset),
		.intf(imem_if) );

Sim_memory #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem
	(	.clk(clk),
		.reset(reset),
		.intf(dmem_if) );

Pu uut(
	.clk(clk),
	.reset(reset),
	.hold(pu_hold),
	.imem(imem_if),
	.dmem(dmem_if),
	.gout(gout),
	.gin(gin),
	.goe(goe),
	.ctrl(pu_ctrl_if),
	.timer(timer_if)
);

assign
	pu_ctrl_if.wakeup = 1'b0,
	pu_ctrl_if.doorbell = 1'b0,
	pu_ctrl_if.ext_input = 1'b0;

assign
	timer_if.tbu = '0,
	timer_if.tbl = '0,
	timer_if.dec = '0,
	timer_if.decar = '0,
	timer_if.tcr = '0,
	timer_if.tsr = '0;

//---------------------------------------------------------------------------
// Single instruction level testing program
//---------------------------------------------------------------------------
program single_inst_stim();
	default clocking cb_uut;

	clocking cb_uut @(posedge clk);
		default input #1step output #4;
		output negedge reset;
	endclocking

	`include "direct_instruction_loader.sv"

	Rand_instruction          inst;
	Rand_state                state;
	Direct_instruction_loader loader;
	Predictor                 predictor;
	Validator                 validator;
	Mem_model                 io;
	Mem_model                 mem;
	Sparse_mem_model          sparse_mem;
	Sparse_mem_model          io_mem;

	initial begin
		inst = new();
		sparse_mem = new();
		io_mem = new();
		mem = sparse_mem;
		io = io_mem;
		state = new(mem, io);
		loader = new();
		predictor = new();
		validator = new(predictor, loader);


		clk <= 1'b0;
		reset <= 1'b1;
		pu_hold <= 1'b0;
		gin <= '0;

		// init instruction memory to nops
		for(int i=0; i<(2**IMEM_ADDR_WIDTH); i++) begin
			Inst nop;
// 			Word w;

			nop.d.opcd = Op_ori;
			nop.d.rt = '0;
			nop.d.ra = '0;
			nop.d.d = '0;

// 			w <= nop;
// 			imem.bank[0].mem[i] <= w[7:0];
// 			imem.bank[1].mem[i] <= w[15:8];
// 			imem.bank[2].mem[i] <= w[23:16];
// 			imem.bank[3].mem[i] <= w[31:24];
			imem.mem[i] <= nop;
		end

		// hold reset
		##10 reset <= 1'b0;

		forever begin : loop_instructions
			int wait_time;

			inst.randomize();
			state.randomize();

			if( 0 ) begin
				$display("---");
				$display("instruction = %8h", inst.get());
				for(int i=0; i<32; i++)
					$display("GPR[%0d] = %8h",
						i, state.get_gpr(i));
			end

			validator.validate_start(inst, state);
			//##1;
			##(validator.wait_time(inst));
			pu_hold <= 1'b1;
			##3;

			validate_single_instruction: assert(validator.validate_end());

			pu_hold <= 1'b0;

			reset <= 1'b1;
			state.clear_mem(1024);
			##2;
			reset <= 1'b0;

		end : loop_instructions
	end
	
	//---------------------------------------------------------------------------
	// Coverage of opcodes
	covergroup cg_opcd @(posedge clk);
		coverpoint inst.opcd iff(pu_hold == 1'b0) ;
	endgroup

	cg_opcd cg_opcd_inst = new();
	//---------------------------------------------------------------------------
	// coverage of instruction forms
	covergroup cg_form @(posedge clk);
		coverpoint inst.op_form iff(pu_hold == 1'b0);
	endgroup

	cg_form cg_form_inst = new();
	//---------------------------------------------------------------------------
	// coverage of XO-opcodes
	covergroup cg_xo_form @(posedge clk);
		alu_xo: coverpoint inst.opcd iff(pu_hold == 1'b0) {
			bins xo = {Op_alu_xo};
			bins others[] = default;
		}

		bclr: coverpoint inst.opcd iff(pu_hold == 1'b0) {
			bins bclr = {Op_bclr};
			bins others[] = default;
		}

		xo: coverpoint inst.xo iff(pu_hold == 1'b0);
		x_xo: coverpoint inst.x_xo iff(pu_hold == 1'b0);
		xl_xo: coverpoint inst.xxo iff(pu_hold == 1'b0);
		xfx_xo: coverpoint inst.xfx_xo iff(pu_hold == 1'b0);

		alu_xo_form: cross alu_xo,xo;
		alu_x_form: cross alu_xo,x_xo;
		branch_xl_form: cross bclr,xl_xo;
		move_xfx_form: cross alu_xo, xfx_xo;
	endgroup

	cg_xo_form cg_xo_form_inst = new();
	//---------------------------------------------------------------------------
	// coverage of corner values
	// every Alu_xo operation should be tested with a set of special corner values
	covergroup cg_corner_values @(posedge clk);
		xo: coverpoint inst.xo iff(pu_hold == 1'b0 && inst.op_form == Form_xo) {
			option.weight = 0;
		}

		x_xo: coverpoint inst.x_xo iff(pu_hold == 1'b0 && inst.op_form == Form_x) {
			option.weight = 0;
		}

		xl_xo: coverpoint inst.xxo iff(pu_hold == 1'b0 && inst.op_form == Form_xl) {
			option.weight = 0;
		}

		ra: coverpoint state.gpr[inst.ra] iff(pu_hold == 1'b0
					&& (inst.op_form == Form_xo || inst.op_form == Form_x)) {
			option.weight = 0;
		}

		rb: coverpoint state.gpr[inst.rb] iff(pu_hold == 1'b0 
					&& (inst.op_form == Form_xo || inst.op_form == Form_x)) {
			option.weight = 0;
		}

		ra_corners: coverpoint state.gpr[inst.ra] iff(pu_hold == 1'b0 
					&& (inst.op_form == Form_xo || inst.op_form == Form_x)) 
		{
			option.weight = 0;

			bins min      = { 32'h80000000 };
			bins max      = { 32'h7fffffff };
			bins zero     = { 32'h00000000 };
			bins all_ones = { 32'hffffffff };
			bins others   = default;
		}
		rb_corners: coverpoint state.gpr[inst.rb] iff(pu_hold == 1'b0 
					&& (inst.op_form == Form_xo || inst.op_form == Form_x))
		{
			option.weight = 0;

			bins min      = { 32'h80000000 };
			bins max      = { 32'h7fffffff };
			bins zero     = { 32'h00000000 };
			bins all_ones = { 32'hffffffff };
			bins others   = default;
		}

		ba: coverpoint state.gpr[inst.ba] iff(pu_hold == 1'b0
					&& inst.op_form == Form_x) {
			option.weight = 0;
		}
		bb: coverpoint state.gpr[inst.bb] iff(pu_hold == 1'b0 
					&& inst.op_form == Form_xl) {
			option.weight = 0;
		}

		ba_corners: coverpoint state.gpr[inst.ba] iff(pu_hold == 1'b0 
					&& inst.op_form == Form_xl) 
		{
			option.weight = 0;

			bins min      = { 32'h80000000 };
			bins max      = { 32'h7fffffff };
			bins zero     = { 32'h00000000 };
			bins all_ones = { 32'hffffffff };
			bins others   = default;
		}
		bb_corners: coverpoint state.gpr[inst.bb] iff(pu_hold == 1'b0 
					&& inst.op_form == Form_xl)
		{
			option.weight = 0;

			bins min      = { 32'h80000000 };
			bins max      = { 32'h7fffffff };
			bins zero     = { 32'h00000000 };
			bins all_ones = { 32'hffffffff };
			bins others   = default;
		}

		// xo_total_cov: cross xo, ra, rb;
		// x_total_cov: cross x_xo, ra, rb;
		// xl_total_cov: cross xl_xo, ba, bb;

		xo_corner_cov: cross xo, ra_corners, rb_corners;
		x_corner_cov: cross x_xo, ra_corners, rb_corners;
		xl_corner_cov: cross xl_xo, ba_corners, bb_corners;

	endgroup

	cg_corner_values cg_corner_values_inst = new();
	//---------------------------------------------------------------------------
	
	//---------------------------------------------------------------------------
	// coverage of rc and oe bits for XO form operations
	covergroup cg_xo_bits @(posedge clk);
		xo: coverpoint inst.xo iff(pu_hold == 1'b0  && inst.op_form == Form_xo) {
			option.weight = 0;
		}

		x_xo: coverpoint inst.x_xo iff(pu_hold == 1'b0 && inst.op_form == Form_x) {
			option.weight = 0;
		}

		rc: coverpoint inst.rc iff(pu_hold == 1'b0
					&& (inst.op_form == Form_xo || inst.op_form == Form_x)) {
			option.weight = 0;
		}

		oe: coverpoint inst.oe iff(pu_hold == 1'b0
					&& (inst.op_form == Form_xo || inst.op_form == Form_x)) {
			option.weight = 0;
		}

		cross xo, rc, oe;
		cross x_xo, rc, oe;
	endgroup

	cg_xo_bits cg_xo_bits_inst = new();
	//---------------------------------------------------------------------------

	//---------------------------------------------------------------------------
	covergroup cg_rotate @(posedge clk);
		opcd: coverpoint inst.opcd iff(pu_hold == 1'b0) {
			option.weight = 0;

			bins rlwimi = { Op_rlwimi };
			bins rlwinm = { Op_rlwinm };
			bins rlwnm  = { Op_rlwnm };
			bins others[] = default;
		}

		rb: coverpoint inst.rb iff(pu_hold == 1'b0 && inst.op_form == Form_m) {
			option.weight = 0;
		}

		mb: coverpoint inst.mb iff(pu_hold == 1'b0 && inst.op_form == Form_m) {
			option.weight = 0;
		}

		me: coverpoint inst.me iff(pu_hold == 1'b0 && inst.op_form == Form_m) {
			option.weight = 0;
		}

		rc: coverpoint inst.rc iff(pu_hold == 1'b0 && inst.op_form == Form_m) {
			option.weight = 0;
		}

		rb_corners: coverpoint inst.rb iff(pu_hold == 1'b0 && inst.op_form == Form_m) {
			option.weight = 0;

			bins zero = { 5'b00000 };
			bins ones = { 5'b11111 };
			bins q1   = { [1:7] };
			bins q2   = { [8:15] };
			bins q3   = { [16:23] };
			bins q4   = { [24:30] };
		}

		mb_corners: coverpoint inst.mb iff(pu_hold == 1'b0 && inst.op_form == Form_m) {
			option.weight = 0;

			bins zero = { 5'b00000 };
			bins ones = { 5'b11111 };
			bins q1   = { [1:7] };
			bins q2   = { [8:15] };
			bins q3   = { [16:23] };
			bins q4   = { [24:30] };
		}

		me_corners: coverpoint inst.me iff(pu_hold == 1'b0 && inst.op_form == Form_m) {
			option.weight = 0;

			bins zero = { 5'b00000 };
			bins ones = { 5'b11111 };
			bins q1   = { [1:7] };
			bins q2   = { [8:15] };
			bins q3   = { [16:23] };
			bins q4   = { [24:30] };
		}

		// mask_cov_total: cross opcd, rb, mb, me;
		mask_cov_corners: cross opcd, rb_corners, mb_corners, me_corners;
		rc_cov: cross opcd, rc;
	endgroup

	cg_rotate g_rotate_inst = new();
	//---------------------------------------------------------------------------
	covergroup cg_load_store @(posedge clk);
		instruction: coverpoint {inst.opcd, inst.x_xo} iff(pu_hold == 1'b0) {
			option.at_least = 200;

			wildcard bins lwz = { {Op_lwz, 10'bZ} };
			wildcard bins lwzu = { {Op_lwzu, 10'bZ} };
			wildcard bins lhz = { {Op_lhz, 10'bZ} };
			wildcard bins lhzu = { {Op_lhzu, 10'bZ} };
			wildcard bins lbz = { {Op_lbz, 10'bZ} };
			wildcard bins lbzu = { {Op_lbzu, 10'bZ} };
			wildcard bins stw = { {Op_stw, 10'bZ} };
			wildcard bins stwu = { {Op_stwu, 10'bZ} };
			wildcard bins sth = { {Op_sth, 10'bZ} };
			wildcard bins sthu = { {Op_sthu, 10'bZ} };
			wildcard bins stb = { {Op_stb, 10'bZ} };
			wildcard bins stbu = { {Op_stbu, 10'bZ} };
			bins lwzx = { {Op_alu_xo, Xop_lwzx} };
			bins lhzx = { {Op_alu_xo, Xop_lhzx} };
			bins lbzx = { {Op_alu_xo, Xop_lbzx} };
			bins stwx = { {Op_alu_xo, Xop_stwx} };
			bins sthx = { {Op_alu_xo, Xop_sthx} };
			bins stbx = { {Op_alu_xo, Xop_stbx} };
			bins lwzux = { {Op_alu_xo, Xop_lwzux} };
			bins lhzux = { {Op_alu_xo, Xop_lhzux} };
			bins lbzux = { {Op_alu_xo, Xop_lbzux} };
			bins stwux = { {Op_alu_xo, Xop_stwux} };
			bins sthux = { {Op_alu_xo, Xop_sthux} };
			bins stbux = { {Op_alu_xo, Xop_stbux} };
			bins others[] = default;
		}

		inst_word: coverpoint {inst.opcd, inst.x_xo} iff(pu_hold == 1'b0) {
			option.weight = 0;
			wildcard bins word_access = { 
				{Op_lwz, 10'bZ}, 
				{Op_stw, 10'bZ},
				{Op_alu_xo, Xop_lwzx},
				{Op_alu_xo, Xop_stwx}
			};
			bins others[] = default;
		}

		inst_halfword: coverpoint {inst.opcd, inst.x_xo} iff(pu_hold == 1'b0) {
			option.weight = 0;
			wildcard bins halfword_access = { 
				{Op_lhz, 10'bz},
				{Op_sth, 10'bz},
				{Op_alu_xo, Xop_lhzx},
				{Op_alu_xo, Xop_sthx}
			};
			bins others[] = default;
		}

		word_aligned: coverpoint (inst.d + state.gpr[inst.ra]) iff(pu_hold == 1'b0) {
			option.weight = 0;
			wildcard bins aligned = { 30'bZ, 2'b00 };
			bins others = default;
		}

		halfword_aligned: coverpoint (inst.d + state.gpr[inst.ra]) iff(pu_hold == 1'b0) {
			option.weight = 0;
			wildcard bins aligned = { {30'bZ, 2'b00}, {30'bZ, 2'b01}, {30'bZ, 2'b10} };
			bins others = default;
		}

		cov_word_aligned: cross inst_word, word_aligned {
			option.at_least = 100;
		}

		cov_halfword_aligned: cross inst_halfword, halfword_aligned {
			option.at_least = 100;
		}
	endgroup

	cg_load_store cg_load_store_inst = new ();
	//---------------------------------------------------------------------------

	//---------------------------------------------------------------------------
	covergroup cg_reg_to_reg @(posedge clk);
		move_spr: coverpoint {inst.opcd, inst.xfx_xo} iff(pu_hold == 1'b0) {
			option.at_least = 100;

			bins mtspr = { {Op_alu_xo, Xop_mtspr} };
			bins mfspr = { {Op_alu_xo, Xop_mfspr} };
			bins others = default;
		}

		spr: coverpoint inst.spr iff(pu_hold == 1'b0) {
			bins xer  = { Spr_xer };
			bins lnk  = { Spr_lnk };
			bins ctr  = { Spr_ctr };
			bins gout = { Spr_gout };
			bins gin  = { Spr_gin };
			bins others = default;
		}

		move_implemented_spr: cross move_spr, spr;
	endgroup

	cg_reg_to_reg cg_reg_to_reg_inst = new();
	//---------------------------------------------------------------------------

endprogram

single_inst_stim prog();


//---------------------------------------------------------------------------


endmodule

