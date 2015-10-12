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

/** Multiplier using the DesignWare sequential multiplier */
module Mul_pipe
	#(	parameter bit REGISTER_MUL_OUT = 1'b1,
			parameter bit REGISTER_RESULT = 1'b1)
	(	input logic     clk, reset,
		input logic     en,
		input logic     uns,
		input Word      a, b,
		output logic    ready,
		output logic    complete,
		output Word     res_hi, res_lo,
		output Cr_field crf_hi, crf_lo );

//---------------------------------------------------------------------------
// Local signals
//---------------------------------------------------------------------------

//localparam integer LATENCY = 1;

Word   next_res_hi, next_res_lo;
//logic[0:LATENCY-1]  busy_sreg;
logic  busy;
logic[65:0] p_i;

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
////DW02_mult_4_stage #(
//DW02_mult_6_stage #(
	//.A_width(DWIDTH),
	//.B_width(DWIDTH)
//) mult (
	//.CLK(clk),
	//.TC(~uns),
	//.A(a),
	//.B(b),
	//.PRODUCT({next_res_hi, next_res_lo})
//);
//DW02_mult_6_stage #(
	//.A_width(DWIDTH+1),
	//.B_width(DWIDTH+1)
//) mult (
	//.CLK(clk),
	//.TC(1'b1),
	//.A({~uns & a[DWIDTH-1], a}),
	//.B({~uns & b[DWIDTH-1], b}),
	//.PRODUCT(p_i)
//);

//xil_mult_uns_6d mult (
	//.ce(1'b1),
	//.clk(clk),
	//.a(a),
	//.b(b),
	//.p(p_i[63:0])
//);
//xil_mult_sgnd_6d mult (
//xil_mult_sgnd_3d mult (
xil_mult_sgnd_3d mult (
//sp6_xil_mult_sgnd_3d mult (
//sp6_xil_mult_sgnd_1d mult (
	.ce(1'b1),
	.clk(clk),
	.a({~uns & a[DWIDTH-1], a}),
	.b({~uns & b[DWIDTH-1], b}),
	.p(p_i)
);

assign {next_res_hi, next_res_lo} = p_i[63:0];

generate if( REGISTER_MUL_OUT == 1'b1 ) begin : gen_reg_out
	always_ff @(posedge clk or posedge reset)
		if( reset )
			{res_hi, res_lo} <= '0;
		else begin
			res_hi <= next_res_hi;
			res_lo <= next_res_lo;
		end
end else begin : gen_no_reg_out
	always_comb begin
		res_hi = next_res_hi;
		res_lo = next_res_lo;
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

	unique if( next_res_hi[$left(next_res_hi)] == 1'b1 ) begin  // negative
		next_crf_hi.lt = 1'b1;
	end else if( (| next_res_hi[DWIDTH-1:0]) == 1'b0 )  // zero
		next_crf_hi.eq = 1'b1;
	else begin // positive
		next_crf_hi.gt = 1'b1;
	end

	unique if( next_res_lo[$left(next_res_lo)] == 1'b1 ) begin  // negative
		next_crf_lo.lt = 1'b1;
	end else if( (| next_res_lo[DWIDTH-1:0]) == 1'b0 )  // zero
		next_crf_lo.eq = 1'b1;
	else begin // positive
		next_crf_lo.gt = 1'b1;
	end

	// overflow if result can not be represented in the low word
	// -> check equivalency of low word sign bit and all high word bits
	next_crf_lo.ov = (| ({DWIDTH {next_res_lo[$left(next_res_lo)]}} ^ next_res_hi));
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
