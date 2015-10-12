// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


//`ifndef JTAG_TRANS__
//`define JTAG_TRANS__

//---------------------------------------------------------------------------
class Jtag_trans;
	virtual interface Jtag_pin_if jtag = null;
	const time clk_period = 100ns;

	extern function new(virtual interface Jtag_pin_if jtag_pins);

	/** Go to reset state by holding tms high for five tck cycles */
	extern task reset();

	/** Got from the reset to the idle state */
	extern task reset_to_idle();

	/** Load an instruction into the JTAG instruction register */
	extern task load_instruction(input logic inst[]);

	/** Load a data word into the JTAG data register selected by
	 * the current instruction */
	extern task load_data(input logic data[]);

	/** Same as load_data, but returns the shifted out value in rdata */
	extern task load_data_read(input logic data[], output logic rdata[]);

	/** Perform one JTAG clock cycle
	 *
	 * sets tms and tdi and returns tdo */
	extern task tick(input tms, tdi, output tdo);
endclass
//---------------------------------------------------------------------------
function
Jtag_trans::new(virtual interface Jtag_pin_if jtag_pins);
	jtag = jtag_pins;
endfunction
//---------------------------------------------------------------------------
task
Jtag_trans::reset();
	jtag.tms <= 1'b1;
	jtag.tdi <= 1'b0;
	//##(5) jtag.tms <= 1'b0;
	#(5*clk_period) jtag.tms <= 1'b0;
endtask
//---------------------------------------------------------------------------
task
Jtag_trans::reset_to_idle();
	logic tdo;
	tick(1'b0, 1'b0, tdo);
endtask
//---------------------------------------------------------------------------
task
Jtag_trans::load_instruction(input logic inst[]);
	logic tdo;
	
	// start in IDLE
	tick(1'b1, 1'b0, tdo);  // go to SELECT-DR-SCAN
	tick(1'b1, 1'b0, tdo);  // go to SELECT-IR-SCAN
	tick(1'b0, 1'b0, tdo);  // go to CAPTURE-IR
	tick(1'b0, 1'b0, tdo);  // go to SHIFT-IR

	for(int i=0; i<inst.size(); i++) 
		tick((i==inst.size()-1) ? 1'b1 : 1'b0,
				inst[i], tdo);  // shift bits in SHIFT-IR

	tick(1'b1, 1'b0, tdo);  // go to UPDATE-IR
	tick(1'b0, 1'b0, tdo);  // return to IDLE
endtask
//---------------------------------------------------------------------------
task
Jtag_trans::load_data(input logic data[]);
	logic tdo;

	// start in IDLE
	tick(1'b1, 1'b0, tdo);  // go to SELECT-DR-SCAN
	tick(1'b0, 1'b0, tdo);  // go to CAPTURE-DR
	tick(1'b0, 1'b0, tdo);  // go to SHIFT-DR

	for(int i=0; i<data.size(); i++)
		tick((i==data.size()-1) ? 1'b1 : 1'b0,
				data[i], tdo);

	tick(1'b1, 1'b0, tdo);  // go to UPDATE-DR
	tick(1'b0, 1'b0, tdo);  // return to IDLE
endtask
//---------------------------------------------------------------------------
task
Jtag_trans::load_data_read(input logic data[], output logic rdata[]);
	logic tdo;
	rdata = new [data.size()];

	// start in IDLE
	tick(1'b1, 1'b0, tdo);  // go to SELECT-DR-SCAN
	tick(1'b0, 1'b0, tdo);  // go to CAPTURE-DR
	tick(1'b0, 1'b0, tdo);  // go to SHIFT-DR

	for(int i=0; i<data.size(); i++)
		tick((i==data.size()-1) ? 1'b1 : 1'b0,
				data[i], rdata[i]);

	tick(1'b1, 1'b0, tdo);  // go to UPDATE-DR
	tick(1'b0, 1'b0, tdo);  // return to IDLE
endtask
//---------------------------------------------------------------------------
task
Jtag_trans::tick(input tms, tdi, output tdo);
	jtag.tms <= tms;
	jtag.tdi <= tdi;
	//##(1) tdo = jtag.tdo;
	#(clk_period) tdo = jtag.tdo;
endtask
//---------------------------------------------------------------------------

//`endif
