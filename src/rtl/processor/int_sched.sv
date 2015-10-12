// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Interrupt scheduler
*
* Decides when to take which interrupt depending on the signaled exceptions.
* It also saves state and sets the syndrome registers depending on the
* exception */
module Int_sched 
	(	input logic clk, reset,

		Int_sched_if.int_sched       intf,
		Register_file_if.int_sched   reg_file,
		Timer_if.int_sched           timer,

		output Frontend::Interrupt_control ictrl
	);

import Pu_types::*;
import Pu_interrupt::*;

//---------------------------------------------------------------------------
// Internal signals
//---------------------------------------------------------------------------

logic    ext_input_ack;
logic    doorbell_ack;
logic    other_ack;
logic    effective_ee;


assign effective_ee = reg_file.msr.ee & ~intf.block_external & ~intf.block;

//---------------------------------------------------------------------------
function automatic void save_state(input Address pc, Msr msr, 
						 output logic srr_we, Word srr0_in, srr1_in);
	srr_we = 1'b1;
	srr0_in = {pc[DWIDTH-3:0], 2'b0};
	srr1_in = msr;

	`ifndef SYNTHESIS
		//$display("saving state: SRR0 = %h, SRR1 = %h",
			//pc, msr);
	`endif /** SYNTHESIS */
endfunction

function automatic void msr_set_base(output Msr msr_in, logic msr_we);
	msr_in = '0;
	msr_we = 1'b1;

	msr_in.ce = reg_file.msr.ce;
	msr_in.me = reg_file.msr.me;
	msr_in.de = reg_file.msr.de;
endfunction

function automatic void restore_state(input logic act, Word srr, inout Msr msr_in, logic msr_we);
	if( act ) begin
		msr_in = srr;
		msr_we = 1'b1;
	end
endfunction
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
always_comb
begin
	// default assignments
	//{>>{ictrl}} = {$bits(ictrl){1'b0}};  // set everything to zero
	ictrl.fb_taken = 1'b0;
	ictrl.fb_not_taken = 1'b0;
	ictrl.fb_pc = '0;
	ictrl.jump = 1'b0;
	ictrl.jump_vec = '0;
	reg_file.srr_we = 1'b0;
	reg_file.csrr_we = 1'b0;
	reg_file.mcsrr_we = 1'b0;
	reg_file.msr_we = 1'b0;
	reg_file.dear_we = 1'b0;
	reg_file.esr_we = 1'b0;
	ext_input_ack = 1'b0;
	doorbell_ack = 1'b0;
	other_ack = 1'b0;

	// design compiler crashes when assigning 'x
	//reg_file.srr0_in = 'x;
	//reg_file.srr1_in = 'x;
	//reg_file.csrr0_in = 'x;
	//reg_file.csrr1_in = 'x;
	//reg_file.mcsrr0_in = 'x;
	//reg_file.mcsrr1_in = 'x;
	//reg_file.msr_in = 'x;
	//reg_file.esr_in = 'x;
	//reg_file.dear_in = 'x;
	
	reg_file.srr0_in = '0;
	reg_file.srr1_in = '0;
	reg_file.csrr0_in = '0;
	reg_file.csrr1_in = '0;
	reg_file.mcsrr0_in = '0;
	reg_file.mcsrr1_in = '0;
	reg_file.msr_in = '0;
	reg_file.esr_in = '0;
	reg_file.dear_in = '0;

	if( intf.base_alignment && !intf.block ) begin
		ictrl.jump = 1'b1;
		ictrl.jump_vec = IVO_ALIGNMENT;

		//$display("unaligned!");

		save_state(intf.pc_alignment, reg_file.msr,
			reg_file.srr_we, reg_file.srr0_in, reg_file.srr1_in);
		msr_set_base(reg_file.msr_in, reg_file.msr_we);
		
		//reg_file.dear_in = 32'bx;   // TODO detemine data exception address
		//reg_file.dear_we = 1'b1;
		
		reg_file.esr_in = '0;
		//reg_file.esr_in.st = 1'bx;  // TODO determine whether access was a store
		reg_file.esr_we = 1'b1;
	end else if( intf.base_trap && !intf.block ) begin
		ictrl.jump = 1'b1;
		ictrl.jump_vec = IVO_PROGRAM;

		//$display("It's a TRAP!");
		
		// should that not be pc_hist[0]?
		// -> no, because SRR0 should point to the causing instruction
		save_state(intf.pc_trap, reg_file.msr,
			reg_file.srr_we, reg_file.srr0_in, reg_file.srr1_in);
		msr_set_base(reg_file.msr_in, reg_file.msr_we);

		reg_file.esr_in = '0;
		reg_file.esr_in.ptr = 1'b1;
		reg_file.esr_we = 1'b1;
	end else if( intf.base_ext_input && effective_ee ) begin
		ictrl.jump = 1'b1;
		ictrl.jump_vec = IVO_EXT_INPUT;
		ext_input_ack = 1'b1;

		//$display("pin trigger");

		save_state(intf.pc, reg_file.msr,
			reg_file.srr_we, reg_file.srr0_in, reg_file.srr1_in);
		msr_set_base(reg_file.msr_in, reg_file.msr_we);
	end else if( timer.tsr.fis && timer.tcr.fie && effective_ee ) begin
		ictrl.jump = 1'b1;
		ictrl.jump_vec = IVO_FIT;
		other_ack = 1'b1;

		//$display("again and again and again");

		save_state(intf.pc, reg_file.msr,
			reg_file.srr_we, reg_file.srr0_in, reg_file.srr1_in);
		msr_set_base(reg_file.msr_in, reg_file.msr_we);
	end else if( timer.tsr.dis && timer.tcr.die && effective_ee ) begin
		ictrl.jump = 1'b1;
		ictrl.jump_vec = IVO_DECREMENTER;
		other_ack = 1'b1;

		//$display("tea time");

		save_state(intf.pc, reg_file.msr,
			reg_file.srr_we, reg_file.srr0_in, reg_file.srr1_in);
		msr_set_base(reg_file.msr_in, reg_file.msr_we);
	end else if( intf.base_doorbell && effective_ee ) begin
		ictrl.jump = 1'b1;
		ictrl.jump_vec = IVO_DOORBELL;
		doorbell_ack = 1'b1;

		//$display("ring! ring!");

		save_state(intf.pc, reg_file.msr,
			reg_file.srr_we, reg_file.srr0_in, reg_file.srr1_in);
		msr_set_base(reg_file.msr_in, reg_file.msr_we);
	end

	// restore actions
	restore_state(
		.act(intf.rest_base_wb),
		.srr(reg_file.srr1),
		.msr_in(reg_file.msr_in),
		.msr_we(reg_file.msr_we)
	);

	restore_state(
		.act(intf.rest_crit_wb),
		.srr(reg_file.csrr1),
		.msr_in(reg_file.msr_in),
		.msr_we(reg_file.msr_we)
	);

	restore_state(
		.act(intf.rest_mcheck_wb),
		.srr(reg_file.mcsrr1),
		.msr_in(reg_file.msr_in),
		.msr_we(reg_file.msr_we)
	);
end
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		intf.base_ext_input_ack <= 1'b0;
		intf.base_doorbell_ack <= 1'b0;
		intf.other_ack <= 1'b0;
	end else begin
		intf.base_ext_input_ack <= ext_input_ack;
		intf.base_doorbell_ack <= doorbell_ack;
		intf.other_ack <= other_ack;
	end
//---------------------------------------------------------------------------

endmodule


// vim: noexpandtab ts=4 sw=4 softtabstop=0 nosmarttab:
