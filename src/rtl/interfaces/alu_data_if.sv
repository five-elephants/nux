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

interface Alu_data_if;
	Word ina, inb;   // input from decode
	Word outa, outb; // output to ALU

	logic cin;
	//Condition_register cr;   // not supported by synplify
	Word cr;

	/*task automatic decode_set_zero;
		ina = '0;
		inb = '0;
		cin = 1'b0;
	endtask*/

	modport decode
		(	//import decode_set_zero,
			output .a(ina), 
			output .b(inb),
			output cin, cr );

	modport alu(input .a(outa), input .b(outb), input cin, cr);
	modport bypass(input ina, inb, output outa, outb);
endinterface
