// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Implements logic operations on the condition register */
module Cr_logic
	(	input Pu_types::Cr_op               op,
		input Pu_types::Condition_register  cr_in,
		input logic[4:0]                    sel_a,
		input logic[4:0]                    sel_b,
		input logic[4:0]                    sel_t,

		output Pu_types::Condition_register cr_out );

import Pu_types::*;

logic a, b;
logic res;

//---------------------------------------------------------------------------
// select input bits
//---------------------------------------------------------------------------
always_comb begin
	//a = cr_in[sel_a[4:2]][3-sel_a[1:0]];
	//b = cr_in[sel_b[4:2]][3-sel_b[1:0]];

	unique case(sel_a[1:0])
		2'b00:   a = cr_in[sel_a[4:2]][3];
		2'b01:   a = cr_in[sel_a[4:2]][2];
		2'b10:   a = cr_in[sel_a[4:2]][1];
		2'b11:   a = cr_in[sel_a[4:2]][0];
		default: a = 1'bx;
	endcase

	unique case(sel_b[1:0])
		2'b00:   b = cr_in[sel_b[4:2]][3];
		2'b01:   b = cr_in[sel_b[4:2]][2];
		2'b10:   b = cr_in[sel_b[4:2]][1];
		2'b11:   b = cr_in[sel_b[4:2]][0];
		default: b = 1'bx;
	endcase
end

//---------------------------------------------------------------------------
// compute logical operations
//---------------------------------------------------------------------------
always_comb
begin : compute
	unique case(op)
		Cr_and:   res = a & b;
		Cr_or:    res = a | b;
		Cr_nand:  res = ~(a & b);
		Cr_nor:   res = ~(a | b);
		Cr_xor:   res = a ^ b;
		Cr_eqv:   res = ~(a ^ b);
		Cr_andc:  res = a & ~b;
		Cr_orc:   res = a | ~b;
		default:  res = 1'bx;
	endcase
end : compute

//---------------------------------------------------------------------------
// generate result word
//---------------------------------------------------------------------------
always_comb
begin
	cr_out = cr_in;
	//cr_out = cr_in[sel_t[4:2]];

	unique case(sel_t[1:0])
		2'b00:   cr_out[sel_t[4:2]][3] = res;
		2'b01:   cr_out[sel_t[4:2]][2] = res;
		2'b10:   cr_out[sel_t[4:2]][1] = res;
		2'b11:   cr_out[sel_t[4:2]][0] = res;
		default: cr_out = 'x;
	endcase
end

endmodule
