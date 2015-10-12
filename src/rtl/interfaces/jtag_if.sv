// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Interface to the TAP's scan-chain */
interface Jtag_if;
	logic tck;      //!< JTAG test clock from external driver
	logic treset;   //!< JTAG reset
	logic tdo;      //!< JTAG TDO pin
	logic tdi;      //!< JTAG TDI pin
	logic sel;      //!< This scan-chain is selected
	logic shift;    //!< The data register is beeing shifted
	logic capture;  //!< Capture the data to the shift register
	logic update;   //!< Update the data from the shift register
	
	/** Modport for the Test Access Port module */
	modport tap(input tdo, output tck, treset, tdi, sel, shift, capture, 
			update);
	
	/** Modport for the user controlled by the TAP */
	modport user(output tdo, input tck, treset, tdi, sel, shift, capture,
			update);
endinterface