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

interface Alu_ctrl_if;
	logic en;
	Alu_op op;

	logic[4:0] rot_dist;
	logic[4:0] rot_start;
	logic[4:0] rot_stop;

	// control signals for condition register logical operations
	logic[4:0] crl_ba;
	logic[4:0] crl_bb;
	logic[4:0] crl_bt;

	logic[4:0] isel_bc;
	logic      isel_selb;

	logic      multi_cycle;  /**< High from second cycle on for multi-cycle 
							   instructions */
	logic      last_cycle;  /**< High on last cycle of a multi-cycle 
							  instruction */

	logic stall;
	logic fwd_from_alu;
	logic fwd_from_ls;


	/*task automatic decode_set_zero;
		en = '0;
		op = Alu_or;
		rot_dist = '0;
		rot_start = '0;
		rot_stop = '0;
		crl_ba = '0;
		crl_bb = '0;
		crl_bt = '0;
		isel_bc = '0;
		isel_selb = 1'b0;
		multi_cycle = 1'b0;
		last_cycle = 1'b0;
	endtask*/


	modport decode
		(	//import decode_set_zero,
		 	output en,
			output op, 
			output rot_dist, 
			output rot_start, 
			output rot_stop,
			output crl_ba, crl_bb, crl_bt,
			output isel_bc, isel_selb,
			output multi_cycle, last_cycle );

	modport alu
		(	input en,
			input op,
			input rot_dist,
			input rot_start,
			input rot_stop,
			input stall,
			input fwd_from_alu,
			input fwd_from_ls,
			input crl_ba, crl_bb, crl_bt,
			input isel_bc, isel_selb,
			input multi_cycle, last_cycle );

endinterface
