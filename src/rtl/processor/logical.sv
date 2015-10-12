// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Logical functions used by the ALU */
module Logical
	(	input Pu_types::Alu_op     op,
		input Pu_types::Word       a, b,

		output Pu_types::Word      res,
		output Pu_types::Cr_field  cr
	);

import Pu_types::*;

Word res_i;

always_comb
	unique case(op)
		Alu_and:      res_i = a & b;
		Alu_andc:     res_i = a & ~b;
		Alu_or:       res_i = a | b;
		Alu_orc:      res_i = a | ~b;
		Alu_xor:      res_i = a ^ b;
		Alu_nand:     res_i = ~(a & b);
		Alu_nor:      res_i = ~(a | b);
		Alu_eqv:      res_i = ~(a ^ b);
		Alu_cmpb:     res_i = { {8{~(| (a[31:24] ^ b[31:24]) )}}, 
		                        {8{~(| (a[23:16] ^ b[23:16]) )}},
								{8{~(| (a[15: 8] ^ b[15: 8]) )}},
								{8{~(| (a[ 7: 0] ^ b[ 7: 0]) )}} };
		default:      res_i = '0;
	endcase


always_comb begin
	// default assignment
	cr = '0;

	unique if( res_i[$left(res_i)] == 1'b1 ) begin  // negative
		cr.lt = 1'b1;
	end else if( (| res_i[DWIDTH-1:0]) == 1'b0 )  // zero
		cr.eq = 1'b1;
	else begin // positive
		cr.gt = 1'b1;
	end
end

assign res = res_i;

endmodule
