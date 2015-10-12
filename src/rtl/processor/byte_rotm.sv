// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Byte-wise rotate and mask module */
module Byte_rotm
	(	input Pu_types::Word w,
		input logic[1:0] sh,
		input logic[3:0] mask,
		output Pu_types::Word y );

import Pu_types::*;

Word shifted;

always_comb
begin : shifter
	unique case(sh)
		2'b00:   shifted = w;
		2'b01:   shifted = { w[23:0], w[31:24] };
		2'b10:   shifted = { w[15:0], w[31:16] };
		2'b11:   shifted = { w[ 7:0], w[31: 8] };
		default: shifted = 'x;
	endcase
end : shifter

assign y = shifted & { {8{mask[3]}}, {8{mask[2]}}, {8{mask[1]}}, {8{mask[0]}} };

endmodule
