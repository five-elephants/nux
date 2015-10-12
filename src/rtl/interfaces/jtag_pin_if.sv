// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Jtag_pin_if();
	logic tdi;
	logic tdo;
	logic tck;
	logic tms;

	logic tdi_sl, tms_sl;

	/** Delay input signals.
	 *
	 * This is necessary, because
	 * a) The Xilinx JTAG_SIM_VIRTEX5 and BSCAN_VIRTEX5 delay the tck signal
	 *    by half a nanosecond. (They also include $setup and $hold checks.)
	 *    So, the data lines must also be delayed for the client to sample
	 *    the correct values.
	 * b) The clocking block construct, which would allow to elegantly do
	 *    this delay, does not seem to be able to write to interface signals
	 *    in ModelSim 6.5b. */
	`ifdef SYNTHESIS
		assign
			tdi_sl = tdi,
			tms_sl = tms;
	`else  /* SYNTHESIS */
		always @(*) begin
			tdi_sl = #5ns tdi;
			tms_sl = #5ns tms;
		end

		initial $display("This interface delays TDI and TMS by 5ns");
	`endif  /* SYNTHESIS */

	modport master(input tdo, 
			output tdi,
			output tck,
			output tms);

	modport slave(output tdo, 
			input tdi_sl,
			input tck,
			input tms_sl);
endinterface
