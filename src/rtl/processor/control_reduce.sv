// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Reduces the control signals from parallel decode modules to one set of
* control signals */
module Control_reduce
	#(	parameter int NUM_INPUTS = 5 )
	(	input logic clk, reset,

		input Control_word[0:NUM_INPUTS-1] cws,  // modelsim 10.0 does not work, if this is an unpacked array

		Decode_ctrl_if.decode         ctrl,
		Inst_fetch_ctrl_if.decode     inst_fetch,
		//Alu_ctrl_if.decode            alu,
		Fixedpoint_ctrl_if.decode     fixedpoint,
		Branch_ctrl_if.decode         branch,
		Trap_ctrl_if.decode           trap,
		Load_store_ctrl_if.decode     load_store,
		Write_back_ctrl_if.decode     write_back,
		Data_hazard_ctrl_if.decode    data_hazard,

		Register_file_if.read         register_file,
		Int_sched_if.decode           int_sched
	);

import Pu_types::*;

/*function automatic int ld2ceil(input int x);
int rv;
for(rv=0; x>(2**rv); rv++) begin end
return rv;
endfunction

function automatic int min(input int a, b);
if( a > b )
	return b;
else
	return a;
endfunction

Control_word  reduced;

generate
Control_word levels[0:ld2ceil(NUM_INPUTS)-1][0:NUM_INPUTS-1];

genvar i, j;
for(j=ld2ceil(NUM_INPUTS); j>0; j--) begin : gen_levels
	for(i=0; i<min(2**j, NUM_INPUTS); i++) begin : gen_reduce
		assign levels[j-1][i] = levels[j][i] | levels[j][i+1];
	end : gen_reduce
end : gen_levels
endgenerate*/

Control_word reduced;
Reg_index    gpr_sel_a_d, gpr_sel_b_d, gpr_sel_c_d;

// generate
//	typedef logic[$bits(cws[0])-1:0] Control_word_bits;
// 
//	Control_word_bits levels[0:NUM_INPUTS-1];
// 
//	assign levels[0] = {>> {cws[0]}};
// 
//	genvar i;
//	for(i=1; i<NUM_INPUTS; i++) begin : gen_reduce
//		always_comb begin
//			Control_word_bits cws_strm;
// 
//			cws_strm = {>> {cws[i]}};
//			levels[i] = levels[i-1] | cws_strm;
//		end
//	end : gen_reduce
// 
//	//always_comb {>> {reduced}} = levels[NUM_INPUTS-1];
//	assign reduced = levels[NUM_INPUTS-1];
// endgenerate

generate
	if( NUM_INPUTS == 4 ) begin : gen_4cws
		always_comb reduced = cws[0] | cws[1] | cws[2] | cws[3];
	end else if( NUM_INPUTS == 3 ) begin : gen_3cws
		always_comb reduced = cws[0] | cws[1] | cws[2];
	end else if( NUM_INPUTS == 2 ) begin : gen_2cws
		always_comb reduced = cws[0] | cws[1];
	end else if( NUM_INPUTS == 1 ) begin : gen_1cws
		always_comb reduced = cws[0];
	end
endgenerate

//always_comb
//begin
	//// synthesis translate_off
	//hardcoded_reduce_input: assert(NUM_INPUTS == 4);
	//// synthesis translate_on
	
	//reduced = cws[0] | cws[1] | cws[2] [>| cws[3]<];
//	reduced = {>> {cws[0]}};
//
//	for(int i=1; i<NUM_INPUTS; i++) begin
//		logic[$bits(cws[0])-1:0] cws_strm;
//		cws_strm = {>> {cws[i]}};
//		reduced |= cws_strm;
//	end
//end


/** delay GPR addresses from IF to use for hazard detection */
always_ff @(posedge clk)
begin
	if( !ctrl.hold ) begin
		gpr_sel_a_d <= register_file.gpr_sel_a;
		gpr_sel_b_d <= register_file.gpr_sel_b;

		//if( reduced.if_gpr_c_over )
			//gpr_sel_c_d <= reduced.if_gpr_c;
		//else
			gpr_sel_c_d <= register_file.gpr_sel_c;
	end
end

//---------------------------------------------------------------------------
/** asynchronous outputs */
assign
	inst_fetch.hold_decode = reduced.if_hold,
	inst_fetch.if_wait = reduced.if_wait,
	inst_fetch.gpr_sel_c_over = reduced.if_gpr_c_over,
	inst_fetch.gpr_sel_c = reduced.if_gpr_c,
	
	data_hazard.gpr_a = gpr_sel_a_d, //reduced.gpr_a,
	data_hazard.gpr_b = gpr_sel_b_d, //reduced.gpr_b,
	data_hazard.gpr_c = gpr_sel_c_d, //reduced.gpr_c,
	//data_hazard.gpr_c = ( (reduced.if_gpr_c_over == 1'b1) ? reduced.if_gpr_c : gpr_sel_c_d ),
	data_hazard.read_gpr_a = reduced.read_gpr_a,
	data_hazard.read_gpr_b = reduced.read_gpr_b,
	data_hazard.read_gpr_c = reduced.read_gpr_c,
	data_hazard.write_gpr_dest_alu = reduced.write_gpr_from_alu,
	data_hazard.write_gpr_dest_mem = reduced.write_gpr_from_mem,
	data_hazard.gpr_dest_alu = reduced.gpr_from_alu,
	data_hazard.gpr_dest_mem = reduced.gpr_from_mem,
	data_hazard.read_ctr = reduced.read_ctr,
	data_hazard.read_lnk = reduced.read_lnk,
	data_hazard.read_cr_0 = reduced.read_cr_0,
	data_hazard.read_cr_1 = reduced.read_cr_1,
	data_hazard.read_cr_2 = reduced.read_cr_2,
	data_hazard.read_xer = reduced.read_xer,
	data_hazard.write_ctr = reduced.write_ctr,
	data_hazard.write_lnk = reduced.write_lnk,
	data_hazard.write_cr = reduced.write_cr,
	data_hazard.write_xer = reduced.write_xer,
	data_hazard.read_spr = reduced.read_spr,
	data_hazard.read_spr2 = reduced.read_spr2,
	data_hazard.write_spr = reduced.write_spr,
	data_hazard.spr_src = reduced.spr_src,
	data_hazard.spr_src2 = reduced.spr_src2,
	data_hazard.spr_dest = reduced.spr_dest;

	//register_file.gpr_sel_a = reduced.gpr_a,
	//register_file.gpr_sel_b = reduced.gpr_b,
	//register_file.gpr_sel_c = reduced.gpr_c;
//---------------------------------------------------------------------------
/** output register */
always_ff @(posedge clk or posedge reset)
	if(reset) begin
		//fixedpoint.decode_set_zero();
		//write_back.decode_set_zero();
		//load_store.decode_set_zero();
		//branch.decode_set_zero();
		//trap.decode_set_zero();
		//inst_fetch.gpr_sel_c_over <= 1'b0;
		//inst_fetch.gpr_sel_c <= '0;

		int_sched.rest_base <= 1'b0;
		int_sched.rest_crit <= 1'b0;
		int_sched.rest_mcheck <= 1'b0;
		int_sched.block_external <= 1'b0;
		
		// ALU signals
		fixedpoint.alu_op <= Alu_add;
		fixedpoint.cr_op <= Cr_and;
		fixedpoint.mul_unsigned <= 1'b0;
		fixedpoint.mul_high <= 1'b0;
		fixedpoint.div_unsigned <= 1'b0;
		fixedpoint.sel <= Fu_none;
		fixedpoint.reg_mv <= Rmv_none;
		// branch signals
		branch.en_decode <= '0;
		branch.jump <= '0;
		branch.crbi <= '0;
		branch.cond <= '0;
		branch.mask_cond <= '0;
		branch.ctr_eq <= '0;
		branch.mask_ctr <= '0;
		branch.dec_ctr <= '0;
		branch.save_link <= '0;
		trap.en_dec <= '0;
		trap.to <= '0;
		// load/store signals
		load_store.en_dec <= 1'b0;
		load_store.we <= '0;
		load_store.mode <= Load_word;
		load_store.multiple <= 1'b0;
		load_store.first_cycle <= 1'b0;
		load_store.multiple_inc <= 1'b0;
		// writeback signals
		write_back.gpr_dest_alu <= '0;
		write_back.gpr_dest_mem <= '0;
		write_back.gpr_wr_alu <= '0;
		write_back.gpr_wr_mem <= '0;
		write_back.wr_cr <= '0;
		write_back.record_cr <= '0;
		write_back.record_ca <= '0;
		write_back.record_ov <= '0;
		write_back.spr_we <= '0;
		write_back.spr_sel <= '0;
		write_back.msr_we <= '0;
		write_back.sleep <= 1'b0;
	end else begin
		// default assignment
		//fixedpoint.decode_set_zero();
		//write_back.decode_set_zero();
		//load_store.decode_set_zero();
		//branch.decode_set_zero();
		//trap.decode_set_zero();

		//inst_fetch.gpr_sel_c_over <= 1'b0;
		//inst_fetch.gpr_sel_c <= '0;
		
		int_sched.rest_base <= 1'b0;
		int_sched.rest_crit <= 1'b0;
		int_sched.rest_mcheck <= 1'b0;
		int_sched.block_external <= 1'b0;
		
		// ALU signals
		fixedpoint.alu_op <= Alu_add;
		fixedpoint.cr_op <= Cr_and;
		fixedpoint.mul_unsigned <= 1'b0;
		fixedpoint.mul_high <= 1'b0;
		fixedpoint.div_unsigned <= 1'b0;
		fixedpoint.sel <= Fu_none;
		fixedpoint.reg_mv <= Rmv_none;
		// branch signals
		branch.en_decode <= '0;
		branch.jump <= '0;
		branch.crbi <= '0;
		branch.cond <= '0;
		branch.mask_cond <= '0;
		branch.ctr_eq <= '0;
		branch.mask_ctr <= '0;
		branch.dec_ctr <= '0;
		branch.save_link <= '0;
		trap.en_dec <= '0;
		trap.to <= '0;
		// load/store signals
		load_store.en_dec <= 1'b0;
		load_store.we <= '0;
		load_store.mode <= Load_word;
		load_store.multiple <= 1'b0;
		load_store.first_cycle <= 1'b0;
		load_store.multiple_inc <= 1'b0;
		// writeback signals
		write_back.gpr_dest_alu <= '0;
		write_back.gpr_dest_mem <= '0;
		write_back.gpr_wr_alu <= '0;
		write_back.gpr_wr_mem <= '0;
		write_back.wr_cr <= '0;
		write_back.record_cr <= '0;
		write_back.record_ca <= '0;
		write_back.record_ov <= '0;
		write_back.spr_we <= '0;
		write_back.spr_sel <= '0;
		write_back.msr_we <= '0;
		write_back.sleep <= 1'b0;


		if( !ctrl.hold ) begin
			//inst_fetch.gpr_sel_c_over <= reduced.if_gpr_c_over;
			//inst_fetch.gpr_sel_c <= reduced.if_gpr_c;

			// ALU signals
			fixedpoint.alu_op <= reduced.alu_op;
			fixedpoint.crl_ba <= reduced.alu_crl_ba;
			fixedpoint.crl_bb <= reduced.alu_crl_bb;
			fixedpoint.crl_bt <= reduced.alu_crl_bt;
			fixedpoint.cr_op <= reduced.cr_op;

			fixedpoint.sel <= reduced.fxdp_sel;
			fixedpoint.mul_high <= reduced.mul_high;
			fixedpoint.mul_unsigned <= reduced.mul_unsigned;
			fixedpoint.div_unsigned <= reduced.div_unsigned;
			fixedpoint.src_cr <= reduced.wb_src_cr;
			fixedpoint.reg_mv <= reduced.wb_reg_mv;

			// branch signals
			branch.en_decode <= reduced.branch_en;
			branch.jump <= reduced.br_jump;
			branch.crbi <= reduced.br_crbi;
			branch.cond <= reduced.br_cond;
			branch.mask_cond <= reduced.br_mask_cond;
			branch.ctr_eq <= reduced.br_ctr_eq;
			branch.mask_ctr <= reduced.br_mask_ctr;
			branch.dec_ctr <= reduced.br_dec_ctr;
			branch.save_link <= reduced.br_save_lnk;

			trap.en_dec <= reduced.trap_en;
			trap.to <= reduced.trap_to;

			// load/store signals
			load_store.en_dec <= reduced.ls_en;
			load_store.we <= reduced.ls_we;
			load_store.mode <= reduced.ls_mode;
			load_store.multiple <= reduced.ls_multiple;
			load_store.first_cycle <= reduced.ls_first_cycle;
			load_store.multiple_inc <= reduced.ls_multiple_inc;

			// writeback signals
			write_back.gpr_dest_alu <= reduced.gpr_from_alu;
			write_back.gpr_dest_mem <= reduced.gpr_from_mem;
			write_back.gpr_wr_alu <= reduced.write_gpr_from_alu;
			write_back.gpr_wr_mem <= reduced.write_gpr_from_mem;
			write_back.wr_cr <= reduced.wb_wr_cr;
			write_back.record_cr <= reduced.wb_record_cr;
			write_back.record_ca <= reduced.wb_record_ca;
			write_back.record_ov <= reduced.wb_record_ov;
			write_back.spr_we <= reduced.wb_spr_we;
			write_back.spr_sel <= reduced.wb_spr_sel;
			write_back.msr_we <= reduced.wb_msr_we;
			write_back.sleep <= reduced.wb_sleep;

			// interrupt scheduler signals
			int_sched.rest_base <= reduced.int_rest_base;
			int_sched.rest_crit <= reduced.int_rest_crit;
			int_sched.rest_mcheck <= reduced.int_rest_mcheck;
			int_sched.block_external <= reduced.int_block_external;
		end
	end
//---------------------------------------------------------------------------

endmodule
