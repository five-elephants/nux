// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Dec_load_update
	#(	parameter bit MULTIPHASE = 1'b0 )
	(	input logic             clk, reset,
		Decode_ctrl_if.decode   ctrl,
		Decode_data_if.decode   data,

		output Control_word     cw );

import Pu_types::*;
import Pu_inst::*;

typedef enum logic[1:0] {
	S_DATA = 2'b01,
	S_ADDR = 2'b10
} Cycle_state;

Control_word     cw_i;
logic            active;
Cycle_state      state;
Ls_cycle_counter ls_ctr, next_ls_ctr;

assign cw = cw_i;

/** Detect, wether the instruction word is to be decoded by this module */
always_comb begin
	logic[15:0] cop;

	cop = {data.inst.x.opcd, data.inst.x.xo};
	unique casez(cop)
		{Op_lwzu, 10'bz}, {Op_lbzu, 10'bz}, {Op_lhzu, 10'bz},
		{Op_alu_xo, Xop_lbzux}, {Op_alu_xo, Xop_lhzux}, {Op_alu_xo, Xop_lwzux}:
			active = 1'b1;
		default:
			active = 1'b0;
	endcase
end


/** Set control signals */
always_comb begin
	// default assignment
	next_ls_ctr = ls_ctr;

	if( active ) begin
		logic[15:0] cop;

		//{>> {cw_i}} = {$bits(cw_i){1'b0}};  // default assignment
		cw_i = '0;

		cw_i.alu_en = 1'b1;
		cw_i.ls_en = 1'b1;
		cw_i.read_gpr_a = (| data.inst.x.ra);  // RA != 0
		cw_i.gpr_a = data.inst.x.ra;
		cw_i.gpr_b = data.inst.x.rb;
		cw_i.gpr_from_alu = data.inst.d.ra;
		cw_i.gpr_from_mem = data.inst.d.rt;
		cw_i.alu_op = Alu_add;
		cw_i.fxdp_sel = Fu_alu;

		if( MULTIPHASE == 1'b0 ) begin
			// single-cycle: store data and address simultaneously
			if( ls_ctr == 0 ) begin
				cw_i.write_gpr_from_alu = 1'b1;
				cw_i.write_gpr_from_mem = 1'b1;

				cw_i.if_hold = 1'b0;
				next_ls_ctr = LOAD_STORE_CYCLES;
			end else begin
				cw_i.if_hold = 1'b1;
				next_ls_ctr = ls_ctr -1;
			end
		end else begin
			// two-cycle: store data first, then address
			// hold instruction fetch for one cycle
			if( state == S_DATA ) begin
				if( ls_ctr == 0 )
					cw_i.write_gpr_from_mem = 1'b1;

				cw_i.if_hold = 1'b1;
			end else if( state == S_ADDR ) begin
				if( ls_ctr == 0 )
					cw_i.write_gpr_from_alu = 1'b1;
			end

			if( ls_ctr == 0 ) begin
				cw_i.if_hold = (state == S_ADDR);
				next_ls_ctr = LOAD_STORE_CYCLES;
			end else begin
				cw_i.if_hold = 1'b1;
				next_ls_ctr = ls_ctr -1;
			end
		end

		// set load_store mode
		cop = {data.inst.x.opcd, data.inst.x.xo};
		unique casez(cop)
			{Op_lbzu, 10'bz},
			{Op_alu_xo, Xop_lbzux}:
				cw_i.ls_mode = Load_byte;

			{Op_lhzu, 10'bz},
			{Op_alu_xo, Xop_lhzux}:
				cw_i.ls_mode = Load_halfword;

			default:
				cw_i.ls_mode = Load_word;
		endcase

		// set read of GPR port B
		unique case(cop)
			{Op_alu_xo, Xop_lbzux}, {Op_alu_xo, Xop_lhzux}, {Op_alu_xo, Xop_lwzux}:
				cw_i.read_gpr_b = 1'b1;
			default:
				cw_i.read_gpr_b = 1'b0;
		endcase
	end else begin
		//{>> {cw_i}} = {$bits(cw_i){1'b0}};
		cw_i = {$bits(cw_i){1'b0}};
	end
end

always_ff @(posedge clk or posedge reset)
	if( reset )
		ls_ctr <= LOAD_STORE_CYCLES;
	else
		ls_ctr <= next_ls_ctr;

generate

	if( MULTIPHASE == 1'b1 ) begin : gen_state_ff
		always_ff @(posedge clk or posedge reset)
			if( reset )
				state <= S_DATA;
			else begin
				if( active && !ctrl.hold ) begin
					unique case(state)
						S_DATA:  state <= S_ADDR;
						S_ADDR:  state <= S_DATA;
					endcase
				end
			end
	end : gen_state_ff

endgenerate
		

endmodule
