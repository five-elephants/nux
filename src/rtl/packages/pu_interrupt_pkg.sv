// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Definitions for exceptions handling and interrupt generation */
package Pu_interrupt;
	/** Type used to signal machine check exceptions */
	typedef struct {
		logic mcheck;
	} Except_mcheck;

	/** Type used to signal critical exceptions */
	typedef struct {
		// exceptions causing the critical input interrupt
		logic cinput;

		// exceptions causing the doorbell critical interrupt
		logic cdoorbell;
	} Except_critical;

	/** Type used to signal base exceptions */
	typedef struct {
		// exceptions causing data storage interrupt
		//logic  d_access;

		// exceptions causing inst storage interrupt
		//logic  i_access;

		// external input interrupt
		logic  ext_input;

		// alignment interrupt
		logic  alignment;

		// program interrupt
		logic  illegal;
		logic  trap;
		logic  unimplemented;

		// doorbell interrupt
		logic  doorbell;
	} Except_base;


	/** Interrupt vector fixed addresses 
	*
	* These are word addresses (therefore the right shift by two). */
	// PowerISA 2.06 definitions -- start
	//const logic[11:0] IVO_MCHECK       = (12'h000 >> 2);
	//const logic[11:0] IVO_CINPUT       = (12'h020 >> 2);
	//const logic[11:0] IVO_DATA_STORAGE = (12'h060 >> 2);
	//const logic[11:0] IVO_INST_STORAGE = (12'h080 >> 2);
	//const logic[11:0] IVO_EXT_INPUT    = (12'h0a0 >> 2);
	//const logic[11:0] IVO_ALIGNMENT    = (12'h0c0 >> 2);
	//const logic[11:0] IVO_PROGRAM      = (12'h0e0 >> 2);
	//const logic[11:0] IVO_SYSCALL      = (12'h120 >> 2);
	//const logic[11:0] IVO_DOORBELL     = (12'h280 >> 2);
	//const logic[11:0] IVO_CDOORBELL    = (12'h2a0 >> 2);
	// PowerISA 2.06 definitions -- end

	// my own definitions -- start
	const logic[11:0] IVO_MCHECK       = 12'h001;
	const logic[11:0] IVO_CINPUT       = 12'h002;
	const logic[11:0] IVO_DATA_STORAGE = 12'h003;
	const logic[11:0] IVO_INST_STORAGE = 12'h004;
	const logic[11:0] IVO_EXT_INPUT    = 12'h005;
	const logic[11:0] IVO_ALIGNMENT    = 12'h006;
	const logic[11:0] IVO_PROGRAM      = 12'h007;
	const logic[11:0] IVO_SYSCALL      = 12'h008;
	const logic[11:0] IVO_DOORBELL     = 12'h009;
	const logic[11:0] IVO_CDOORBELL    = 12'h00a;
	const logic[11:0] IVO_FIT          = 12'h00b;
	const logic[11:0] IVO_DECREMENTER  = 12'h00c;
	// my own definitions -- end


	/** Interrupt controller control register */
	typedef struct packed {
		logic[31:20] reserved_2;
		logic[3:0] gin_sense_level;  //< 1: trigger on level, 0: trigger on edge
		logic[3:0] gin_trigger;      //< 0: trigger on high level or rising edge
		logic[3:0] gin_mask;         //< enable pins individually
		logic[7:1] reserved;
		logic doorbell_en;           //< enable the doorbell interrupt
	} Int_ctrl_reg;

endpackage
