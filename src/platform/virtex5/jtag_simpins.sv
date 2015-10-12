// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Jtag_simpins(Jtag_pin_if.slave pins);
/** JTAG access for Virtex-5 FPGAs */
JTAG_SIM_VIRTEX5 jtag_sim
	(	.TDO(pins.tdo),
		.TDI(pins.tdi_sl),
		.TCK(pins.tck),
		.TMS(pins.tms_sl) );
endmodule
