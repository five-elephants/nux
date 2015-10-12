// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Exts
	(	input Pu_types::Alu_op  op,
		input Pu_types::Word    win,

		output Pu_types::Word   wout );

import Pu_types::*;

always_comb
	unique case(op)
		Alu_esb:
			wout = { {24{win[7]}}, win[7:0] };

		Alu_esh:
			wout = { {16{win[15]}}, win[15:0] };

		default:
			wout = win;
	endcase

endmodule
