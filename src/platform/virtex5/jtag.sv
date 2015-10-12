// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/**! Module for Virtex-5 specific JTAG access */
module Jtag
	#(	int CHAIN = 1 )
	(	Jtag_if.tap   intf );



// BSCAN_VIRTEX5: Boundary Scan primitive for connecting internal
//                logic to JTAG interface.
//                Virtex-5
// Xilinx HDL Libraries Guide, version 11.2
BSCAN_VIRTEX5 #(.JTAG_CHAIN(CHAIN)) BSCAN_VIRTEX5_inst 
	(	.CAPTURE(intf.capture),
		.DRCK(intf.tck),
		.RESET(intf.treset),
		.SEL(intf.sel),
		.SHIFT(intf.shift),
		.TDI(intf.tdi),
		.UPDATE(intf.update),
		.TDO(intf.tdo) );

// End of BSCAN_VIRTEX5_inst instantiation


endmodule
