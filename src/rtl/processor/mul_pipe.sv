// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Multiplier using the DesignWare pipelined multiplier */
module Mul_pipe
	#(	parameter bit REGISTER_MUL_OUT = 1'b1,
		parameter bit REGISTER_RESULT = 1'b1)
	(	input logic               clk, reset,
		input logic               en,
		input logic               uns,
		input Pu_types::Word      a, b,
		output logic              ready,
		output logic              complete,
		output Pu_types::Word     res_hi, res_lo,
		output Pu_types::Cr_field crf_hi, crf_lo);

import Pu_types::*;

localparam int MULT_STAGES = Frontend::mul_latency - REGISTER_MUL_OUT - REGISTER_RESULT;

initial assert(MULT_STAGES >= 2) else
	$error("DW_mult_pipe must have at least two stages.");
//---------------------------------------------------------------------------
// Local signals
//---------------------------------------------------------------------------

//localparam integer LATENCY = 1;

Word                res_hi_i, res_lo_i;
//logic[0:LATENCY-1]  busy_sreg;
logic               busy;

//---------------------------------------------------------------------------
// static assignments
//---------------------------------------------------------------------------

assign ready = 1'b1;

always_ff @(posedge clk or posedge reset)
	if( reset )
		busy <= 1'b1;
	else
		if( en )
			busy <= ~busy;
		else
			busy <= 1'b1;

assign complete = ~busy;

//---------------------------------------------------------------------------
// Multiplier
//---------------------------------------------------------------------------

//DW02_mult_2_stage #(
//DW02_mult_4_stage #(
/*DW02_mult_6_stage #(
	.A_width(DWIDTH),
	.B_width(DWIDTH)
) mult (
	.CLK(clk),
	.TC(~uns),
	.A(a),
	.B(b),
	.PRODUCT({res_hi_i, res_lo_i})
);*/

DW_mult_pipe #(
	.a_width(DWIDTH),
	.b_width(DWIDTH),
	.num_stages(MULT_STAGES),
	.stall_mode(0),
	.rst_mode(1),
	.op_iso_mode(0)
) mult (
	.clk(clk),
	.rst_n(~reset),
	.en(1'b1),       // not used when stall_mode == 0
	.tc(~uns),
	.a(a),
	.b(b),
	.product({res_hi_i, res_lo_i})
);

generate if( REGISTER_MUL_OUT == 1'b1 ) begin : gen_reg_out
	always_ff @(posedge clk or posedge reset)
		if( reset )
			{res_hi, res_lo} <= '0;
		else
			{res_hi, res_lo} <= {res_hi_i, res_lo_i};
end else begin : gen_no_reg_out
	always_comb begin
		res_hi = res_hi_i;
		res_lo = res_lo_i;
	end
end
endgenerate

//---------------------------------------------------------------------------
// Generate compare bits
//---------------------------------------------------------------------------
Cr_field next_crf_lo;
Cr_field next_crf_hi;

always_comb begin
	// default assignment
	next_crf_lo = '0;
	next_crf_hi = '0;

	unique if( res_hi_i[$left(res_hi_i)] == 1'b1 ) begin  // negative
		next_crf_hi.lt = 1'b1;
	end else if( (| res_hi_i[DWIDTH-1:0]) == 1'b0 )  // zero
		next_crf_hi.eq = 1'b1;
	else begin // positive
		next_crf_hi.gt = 1'b1;
	end

	unique if( res_lo_i[$left(res_lo_i)] == 1'b1 ) begin  // negative
		next_crf_lo.lt = 1'b1;
	end else if( (| res_lo_i[DWIDTH-1:0]) == 1'b0 )  // zero
		next_crf_lo.eq = 1'b1;
	else begin // positive
		next_crf_lo.gt = 1'b1;
	end

	// overflow if result can not be represented in the low word
	// -> check equivalency of low word sign bit and all high word bits
	next_crf_lo.ov = (| ({DWIDTH {res_lo_i[$left(res_lo_i)]}} ^ res_hi_i));
end

generate if( REGISTER_RESULT == 1'b1 ) begin : gen_reg_result
	always_ff @(posedge clk or posedge reset)
		if( reset ) begin
			crf_hi <= '0;
			crf_lo <= '0;
		end else begin
			crf_hi <= next_crf_hi;
			crf_lo <= next_crf_lo;
		end
end else begin : gen_no_reg_result
	always_comb begin
		crf_hi = next_crf_hi;
		crf_lo = next_crf_lo;
	end
end
endgenerate

//---------------------------------------------------------------------------

endmodule

/* vim: set noet fenc= ff=unix sts=0 sw=4 ts=4 : */
