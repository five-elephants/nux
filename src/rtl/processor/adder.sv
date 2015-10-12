// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** A word adder for use by the ALU 
* 
* op can be Alu_add, Alu_sub, Alu_neg, Alu_cmp or Alu_cmpl.
* Compare operations work just like subtractions, only the calculation of the
* condition bits is more complicated.
* */
module Adder
	(	input Pu_types::Alu_op                op,
		input Pu_types::Word                  a,
		input Pu_types::Word                  b,
		input logic                           cin,

		output Pu_types::Word                 res,
		output logic                          cout,
		output Pu_types::Cr_field             cr
	);

import Pu_types::*;

Word   res_i;
logic  overflow;
logic  an, bn, yn;
logic  inv_a;

assign an = a[$left(a)] ^ inv_a;
assign bn = b[$left(b)];
assign yn = res_i[$left(res_i)];

always_comb
	unique case(op)
		Alu_sub, Alu_neg, Alu_cmp, Alu_cmpl: begin
			inv_a = 1'b1;
		end

		// Alu_add:
		default: begin
			inv_a = 1'b0;
		end
	endcase

assign cout = an & bn | (yn ^ an ^ bn) & (an | bn);
assign overflow = (an & bn | (yn ^ an ^ bn) & (an | bn)) ^ (yn ^ an ^ bn);

assign res_i = (a ^ {DWIDTH{inv_a}}) + b + cin;
	
always_comb begin
	logic cmp, cmp_logical;

	// default assignment
	cr = '0;
	cmp = 1'b0;
	cmp_logical = 1'b0;


	if( op == Alu_cmp )
		cmp = 1'b1;
	else if( op == Alu_cmpl ) begin
		cmp = 1'b1;
		cmp_logical = 1'b1;
	end

	cr.ov = overflow & ~(cmp | cmp_logical);
	// calculate compare bits
	unique if( res_i[$left(res_i)] == 1'b1 ) begin  // negative
		logic c;
		c = (a[DWIDTH-1] ^ b[DWIDTH-1]) & cmp_logical;
		cr.lt = (~(overflow & cmp) ^ c) ^ cmp;
		cr.gt = ( (overflow & cmp) ^ c) ^ cmp;
	end else if( (| res_i[DWIDTH-1:0]) == 1'b0 )  // zero
		cr.eq = 1'b1;
	else begin // positive
		logic c;
		c = (a[DWIDTH-1] ^ b[DWIDTH-1]) & cmp_logical;
		cr.lt = ( (overflow & cmp) ^ c) ^ cmp;
		cr.gt = (~(overflow & cmp) ^ c) ^ cmp;
	end
end


assign res = res_i;

endmodule
