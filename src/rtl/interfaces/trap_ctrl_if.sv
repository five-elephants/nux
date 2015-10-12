// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Pu_types::*;

interface Trap_ctrl_if;
	logic       en;
	logic       en_dec, en_int;
	Trap_to     to;

	always_comb en = en_int & en_dec;

	/*task automatic decode_set_zero();
		en_dec = 1'b0;
		to = '0;
	endtask*/

	modport decode ( 
		/*import decode_set_zero, */
		output to,
		output en_dec
	);
	modport trap ( input en, to, en_int );
	modport int_sm ( output en_int );
endinterface
