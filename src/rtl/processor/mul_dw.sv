// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Pipelined multiplier from the DesignWare library 
*
* This doesn't realy offer an advantage over the sequential multiplier,
* because my pipeline architecture is not designed to issue the next mult
* before the previous one has finished. */
module Mul_dw
	(	input logic     clk, reset,
		input logic     en,
		input logic     uns,
		input Word      a, b,
		output Word     res_hi, res_lo,
		output Cr_field crf_hi, crf_lo);

import Pu_types::*;

localparam int STAGES = 4;

logic[2*DWIDTH-1:0]  prod;

// Instance of DW_mult_pipe
DW_mult_pipe 
	#(	.a_width(DWIDTH),
		.b_width(DWIDTH),
		.num_stages(STAGES),
		.stall_mode(1'b1),   // is stallable
		.rst_mode(1) )       // asynchronous reset
	mult_pipe_inst	
	(	.clk(clk),
		.rst_n(~reset),
		.en(en),             // constant on for the moment
		.tc(~uns),
		.a(a),
		.b(b),
		.product(prod) );


assign {res_hi, res_lo} = prod;


always_comb
begin
	Word res_hi_i;
	Word res_lo_i;

	// default assignment
	crf_lo = '0;
	crf_hi = '0;

	res_hi_i = prod[63:32];
	res_lo_i = prod[31: 0];

	unique if( res_hi_i[$left(res_hi_i)] == 1'b1 ) begin  // negative
		crf_hi.lt = 1'b1;
	end else if( (| res_hi_i[DWIDTH-1:0]) == 1'b0 )  // zero
		crf_hi.eq = 1'b1;
	else begin // positive
		crf_hi.gt = 1'b1;
	end

	unique if( res_lo_i[$left(res_lo_i)] == 1'b1 ) begin  // negative
		crf_lo.lt = 1'b1;
	end else if( (| res_lo_i[DWIDTH-1:0]) == 1'b0 )  // zero
		crf_lo.eq = 1'b1;
	else begin // positive
		crf_lo.gt = 1'b1;
	end

	// overflow if result can not be represented in the low word
	// -> check equivalency of low word sign bit and all high word bits
	crf_lo.ov =(| ({DWIDTH {res_lo_i[$left(res_lo_i)]}} ^ res_hi_i));
end


endmodule

