// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Count the number of set bits in Word x.
 *
 * Deassert cnt_bytes to get the number of bits in the complete word.
 * (not implemented!)
 * */
module Popcnt
	(	input Pu_types::Word x,
		input logic cnt_bytes,
		output Pu_types::Word y );

import Pu_types::*;

localparam NUM_BYTES = DWIDTH/8;

logic[0:NUM_BYTES*2-1][2:0] cnt_nibble;
logic[0:NUM_BYTES-1][3:0]   cnt_byte;

//---------------------------------------------------------------------------
generate
	genvar i;
	for(i=0; i<NUM_BYTES; i++) begin : bit_counter
		logic[7:0] bits;
		always_comb for(int b=0; b<8; b++) bits[b] = x[i*8+b];

		Bit_counter_4 low(.bits(bits[3:0]), .cnt(cnt_nibble[i][2:0]));
		Bit_counter_4 high(.bits(bits[7:4]), .cnt(cnt_nibble[i+NUM_BYTES][2:0]));

		assign cnt_byte[i] = {1'b0, cnt_nibble[i]} + {1'b0, cnt_nibble[i+NUM_BYTES]};
	end
endgenerate
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
assign y = {4'b0, cnt_byte[3], 4'b0, cnt_byte[2], 4'b0, cnt_byte[1], 4'b0, cnt_byte[0]};
//---------------------------------------------------------------------------

endmodule
