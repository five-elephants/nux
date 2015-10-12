// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Multiplexer module for the isel instruction
 * */
module Isel
	(	input Pu_types::Alu_op              op,
		input Pu_types::Word                a,
		input Pu_types::Word                b,
		input Pu_types::Condition_register  cr,
		input logic[4:0]          			bc,   /**< Selects the bit in the condition register */
		input logic               			sel_b,  /**< Override for bc to select input b */

		output Pu_types::Word               res,
		output Pu_types::Cr_field           crout
	);

import Pu_types::*;

Word res_i;

always_comb
	if( sel_b ) 
		res_i = b;
	else begin
		unique case(op)
			Alu_isel: begin
				res_i = a;
			end

			default:
				res_i = a;
		endcase
	end


/** Calculate output condition bits */
always_comb
begin
	// default assignments
	crout = '0;

	if( res_i[$left(res_i)] == 1'b1 )  // negative
		crout.lt = 1'b1;
	else if( (| res_i) == 1'b0 )  // zero
		crout.eq = 1'b1;
	else  // positive
		crout.gt = 1'b1;
end


assign res = res_i;

endmodule
