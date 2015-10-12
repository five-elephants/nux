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

interface Bypass_if(input logic clk);
	// control signals
	Bypass_line_ctrl lines;

	// modports
	modport bypass(input lines);
	modport control(output lines);

	//---------------------------------------------------------------------------
	// embeddes assertions
	// synthesis translate_off
	/*check_alu_forwarding_is_unicast: assert property(
		@(posedge clk)
		( $onehot0({lines.alu_to_alu_a, lines.alu_to_alu_b}) )
	);

	check_load_store_forwarding_is_unicast: assert property(
		@(posedge clk)
		( $onehot0({lines.ls_to_alu_a, lines.ls_to_alu_b}) )
	);*/
	// synthesis translate_on
	//---------------------------------------------------------------------------
endinterface
