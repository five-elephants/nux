// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/**! Module for Spartan-6 specific JTAG access */
module Jtag_s6
	#(	int CHAIN = 1 )
	(	Jtag_if.tap   intf );



BSCAN_SPARTAN6 #(.JTAG_CHAIN(CHAIN)) BSCAN_SPARTAN6_inst
	(	.CAPTURE(intf.capture),
		.DRCK(intf.tck),
		.RESET(intf.treset),
		.RUNTEST(),
		.SEL(intf.sel),
		.SHIFT(intf.shift),
		.TCK(),
		.TDI(intf.tdi),
		.TMS(),
		.UPDATE(intf.update),
		.TDO(intf.tdo) );


endmodule
