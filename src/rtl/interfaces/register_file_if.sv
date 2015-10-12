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
import Pu_interrupt::Int_ctrl_reg;

interface Register_file_if
	#(	parameter bit SINGLE_WRITE_PORT = 1'b0 );

	// general purpose register access
	Reg_index gpr_sel_a;
	Word gpr_a;

	Reg_index gpr_sel_b;
	Word gpr_b;

	Reg_index gpr_sel_c;
	Word gpr_c;

	Reg_index gpr_sel_dest;
	logic gpr_we;
	Word gpr_dest;

	/*generate
		if( SINGLE_WRITE_PORT == 1'b0 ) begin : gen_dual_write_port*/
			Reg_index gpr_sel_dest_2;
			logic gpr_we_2;
			Word gpr_dest_2;
		/*end : gen_dual_write_port
	endgenerate*/

	// branch facility registers access
	logic[7:0]         wr_cr;
	Cr_field           cr_in;
	Cr_bits            cr;
	//Word               cr;

	Word ctr;
	Word lnk;
	Word ctr_in;
	logic ctr_we;
	Word lnk_in;
	logic lnk_we;

	Word xer;
	Word xer_in;
	logic xer_we;

	// General I/O register access
	logic gout_we;
	Word gout;
	Word gout_in;
	Word gin;
	Word gin_in;
	Word goe;
	Word goe_in;
	logic goe_we;

	Msr   msr, msr_in;
	logic msr_we;
	Msr   msr_pin;    // second write port
	logic msr_pwe;

	Word  srr0, srr0_in, srr1, srr1_in;
	logic srr_we;
	Word  srr0_pin, srr1_pin;   // second prioritized write port
	logic srr0_pwe, srr1_pwe;


	Word  csrr0, csrr0_in, csrr1, csrr1_in;
	logic csrr_we;
	Word  csrr0_pin, csrr1_pin;   // second prioritized write port
	logic csrr0_pwe, csrr1_pwe;

	Word  mcsrr0, mcsrr0_in, mcsrr1, mcsrr1_in;
	logic mcsrr_we;
	Word  mcsrr0_pin, mcsrr1_pin;   // second prioritized write port
	logic mcsrr0_pwe, mcsrr1_pwe;

	Word  dear, dear_in;
	logic dear_we;
	Word  dear_pin;  // second prioritized write port
	logic dear_pwe;

	Esr   esr, esr_in;
	logic esr_we;
	Esr   esr_pin;  // second prioritized write port
	logic esr_pwe;

	
	Int_ctrl_reg iccr, iccr_in;
	logic        iccr_we;

	modport reg_file (
		input gpr_dest, 
		input gpr_dest_2,
		input gpr_sel_dest, 
		input gpr_sel_dest_2,
		input gpr_we, 
		input gpr_we_2,
		input wr_cr, 
		input cr_in,
		input ctr_in,
		input ctr_we,
		input lnk_in,
		input lnk_we,
		input xer_in,
		input xer_we,
		input gin_in,
		input gout_in,
		input gout_we,
		input goe_we, goe_in,

		input srr0_pin, srr1_pin, srr0_pwe, srr1_pwe,
		input csrr0_pin, csrr1_pin, csrr0_pwe, csrr1_pwe,
		input mcsrr0_pin, mcsrr1_pin, mcsrr0_pwe, mcsrr1_pwe,
		input dear_pin, dear_pwe,
		input esr_pin, esr_pwe,
		input msr_pin, msr_pwe,

		input iccr_in, iccr_we,

		input gpr_sel_a, 
		input gpr_sel_b, 
		input gpr_sel_c,
		output gpr_a, 
		output gpr_b,
		output gpr_c,
		output cr,
		output ctr,
		output lnk,
		output xer,
		output gout,
		output gin,
		output goe,
		output msr, srr0, csrr0, mcsrr0, srr1, csrr1, mcsrr1, dear, esr,
		output iccr,

		input msr_in, esr_in, srr0_in, srr1_in, csrr0_in, csrr1_in, 
		mcsrr0_in, mcsrr1_in, dear_in,
		msr_we, esr_we, srr_we, csrr_we, mcsrr_we, dear_we
  );

	modport write ( 
		output gpr_dest, 
		output gpr_dest_2,
		output gpr_sel_dest, 
		output gpr_sel_dest_2,
		output gpr_we, 
		output gpr_we_2,
		output wr_cr, 
		input cr,
		output cr_in,
		input ctr,
		output ctr_in,
		output ctr_we,
		input lnk,
		output lnk_in,
		output lnk_we,
		input xer,
		output xer_in,
		output xer_we,
		output gout_in,
		output gout_we,
		input gout,
		input gin,
		output goe_we, goe_in,
		input goe,

		output srr0_pin, srr1_pin, srr0_pwe, srr1_pwe,
		output csrr0_pin, csrr1_pin, csrr0_pwe, csrr1_pwe,
		output mcsrr0_pin, mcsrr1_pin, mcsrr0_pwe, mcsrr1_pwe,
		output dear_pin, dear_pwe,
		output esr_pin, esr_pwe,
		output msr_pin, msr_pwe,

		output iccr_in, iccr_we
	);

	modport read ( 
		output gpr_sel_a, 
		output gpr_sel_b, 
		output gpr_sel_c,
		input gpr_a, 
		input gpr_b,
		input gpr_c,
		input cr,
		input ctr,
		input lnk,
		input xer,
		input gout,
		input gin,
		input goe,
		input msr, srr0, csrr0, mcsrr0, srr1, csrr1, mcsrr1, dear, esr,
		input iccr
	);

	modport int_sched (
		input msr, esr, srr1, csrr1, mcsrr1,
		output msr_in, esr_in, srr0_in, srr1_in, csrr0_in, csrr1_in, 
		mcsrr0_in, mcsrr1_in, dear_in,
		msr_we, esr_we, srr_we, csrr_we, mcsrr_we, dear_we
	);

	modport inst_fetch (
		output gpr_sel_a, gpr_sel_b, gpr_sel_c
	);
	  

endinterface


// vim: noexpandtab ts=4 sw=4 softtabstop=0 smarttab:
