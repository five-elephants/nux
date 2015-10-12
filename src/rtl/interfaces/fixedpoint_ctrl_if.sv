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


interface Fixedpoint_ctrl_if(input logic clk, reset);
	logic          en_int;

	Alu_op         alu_op;
	Cr_op          cr_op;

	// control signals for condition register logical operations
	logic[4:0]     crl_ba;
	logic[4:0]     crl_bb;
	logic[4:0]     crl_bt;
	Register_move  reg_mv;
	logic[7:0]     src_cr;


	logic          mul_unsigned;
	logic          mul_high;

	logic          div_unsigned;

	Func_unit      sel;

	Func_unit      sel_d;
	logic          mul_high_d;
	logic[4:0]     crl_bt_d;

	logic          mul_en;
	logic          mul_ready, mul_complete;
	logic          div_en;
	logic          div_ready, div_complete;

	logic          oe, oe_d;
	logic          oe_shreg[0:0];

	//always_ff @(posedge clk or posedge reset)
		//if( reset ) begin
			//sel_d <= Fu_none;
			//mul_high_d <= 1'b0;
			//crl_bt_d <= 5'h0;
		//end else begin
			//sel_d <= sel;
			//mul_high_d <= mul_high;
			//crl_bt_d <= crl_bt;
		//end
	assign
		sel_d = sel,
		mul_high_d = mul_high,
		crl_bt_d = crl_bt;

	assign mul_en = (sel == Fu_mul) && en_int;
	assign div_en = (sel == Fu_div) && en_int;

	/*always_ff @(posedge clk)
	begin
		oe_shreg[0] <= oe;

		for(int i=1; i<=$right(oe_shreg); i++)
			oe_shreg[i] <= oe_shreg[i-1];
	end

	assign oe_d = oe_shreg[$right(oe_shreg)];*/
	assign oe_d = oe;

	/*task automatic decode_set_zero;
		alu_op = Alu_add;
		cr_op = Cr_and;
		mul_unsigned = 1'b0;
		mul_high = 1'b0;
		div_unsigned = 1'b0;
		sel = Fu_none;
		reg_mv = Rmv_none;
	endtask*/
	
	modport decode
		(	//import decode_set_zero,
			output alu_op, cr_op, crl_ba, crl_bb, crl_bt,
			mul_unsigned, mul_high, div_unsigned,
			sel, reg_mv, src_cr, oe);

	modport feedback
		(	input mul_ready, mul_complete, div_ready, div_complete );

	modport internal
		(	input alu_op, cr_op, crl_ba, crl_bb, crl_bt, crl_bt_d,
			mul_unsigned, div_unsigned, reg_mv,
			src_cr,
			input sel_d,
			input mul_high_d,
			input mul_en, div_en,
			input oe_d,
			output mul_ready, mul_complete, div_ready, div_complete
		);

	modport int_sm ( output en_int );
endinterface

// vim: noexpandtab ts=4 sw=4 softtabstop=0 nosmarttab:
