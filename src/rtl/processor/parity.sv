// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Detect if there is an odd number of set LSB in the bytes of x */
module Parity
	(	input Pu_types::Word x,
		output Pu_types::Word y );
		
import Pu_types::*;

assign y[DWIDTH-1:1] = '0;
assign y[0] = x[0] ^ x[8] ^ x[16] ^ x[24];
		
endmodule
