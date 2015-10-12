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

interface Data_hazard_ctrl_if();

	logic en;  // ignores read and write inputs when not set

	Reg_index gpr_a;           //< source register a
	Reg_index gpr_b;           //< source register b
	Reg_index gpr_c;           //< source register c
	Reg_index gpr_dest_alu;    //< target register for ALU
	Reg_index gpr_dest_mem;    //< target register for memory
	logic read_gpr_a;          //< read port a
	logic read_gpr_b;          //< read port b
	logic read_gpr_c;          //< read port c
	logic write_gpr_dest_alu;  //< write from ALU
	logic write_gpr_dest_mem;  //< write from memory
	Fu_port fu_a;              //< target functional unit for read port a
	Fu_port fu_b;              //< target functional unit for read port b
	Fu_port fu_c;              //< target functional unit for read port c

	logic[7:0] read_cr_0, read_cr_1, read_cr_2;
	logic[7:0] write_cr;

	logic read_ctr;
	logic write_ctr;
	
	logic read_lnk;   // TODO must link be explicitly tracked?
	logic write_lnk;

	logic read_xer;
	logic write_xer;

	logic read_spr, read_spr2;
	logic write_spr;
	Spr_reduced spr_src, spr_src2, spr_dest;

/*	task automatic decode_set_zero();
		read_gpr_a = '0;
		read_gpr_b = '0;
		write_gpr_dest = '0;
		read_cr = '0;
		write_cr = '0;
		read_ctr = '0;
		write_ctr = '0;
		read_lnk = '0;
		write_lnk = '0;
	endtask
*/
	//
	// modports
	//

	modport decode
		(	//import decode_set_zero,
		 	output gpr_a,
			output gpr_b,
			output gpr_c,
			output gpr_dest_alu,
			output gpr_dest_mem,
			output read_gpr_a,
			output read_gpr_b,
			output read_gpr_c,
			output write_gpr_dest_alu,
			output write_gpr_dest_mem,
			output read_cr_0, read_cr_1, read_cr_2,
			output write_cr,
			output read_ctr,
			output write_ctr,
			output read_lnk,
			output write_lnk,
			output read_xer,
			output write_xer,
			output read_spr, read_spr2, write_spr, spr_src, spr_src2, spr_dest );

	modport operand_fetch
		(	output fu_a, fu_b, fu_c );

	modport data_hazard_ctrl
		(	input en,
			input gpr_a,
			input gpr_b,
			input gpr_c,
			input gpr_dest_alu,
			input gpr_dest_mem,
			input read_gpr_a,
			input read_gpr_b,
			input read_gpr_c,
			input write_gpr_dest_alu,
			input write_gpr_dest_mem,
			input read_cr_0, read_cr_1, read_cr_2,
			input write_cr,
			input read_ctr,
			input write_ctr,
			input read_lnk,
			input write_lnk,
			input read_xer,
			input write_xer,
			input fu_a, fu_b, fu_c,
			input read_spr, read_spr2, write_spr, spr_src, spr_src2, spr_dest );

	modport inst_fetch 
		(	output en );

endinterface
