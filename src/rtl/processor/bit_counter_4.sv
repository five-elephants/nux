// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Counts the number of set bit in bits. 
 */
module Bit_counter_4
	(	input logic[3:0] bits,
		output logic[2:0] cnt );

	always_comb cnt[2] = bits[3] & bits[2] & bits[1] & bits[0];
    
    always_comb
        unique case(bits)
			4'b0000 , 4'b0001 , 4'b0010 , 4'b0100 , 4'b1000 , 4'b1111:
				cnt[1] = 1'b0;
			default:
				cnt[1] = 1'b1;
		endcase
		
	always_comb
		unique case(bits)
			4'b0001 , 4'b0010 , 4'b0100 , 4'b0111 , 4'b1000 , 4'b1011 , 4'b1101 , 4'b1110:
				cnt[0] = 1'b1;
			default:
				cnt[0] = 1'b0;
		endcase


endmodule
