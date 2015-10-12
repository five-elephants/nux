// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Register_file
	#(	parameter bit SINGLE_WRITE_PORT = 1'b0 )
	(	input logic clk,
		input logic reset,

		Register_file_if.reg_file  reg_file,
		Gpr_file_if.processor      gpr_file
	);

import Pu_types::*;
import Pu_interrupt::Int_ctrl_reg;

Condition_register  cr;
Word                ctr;
Word                lnk;
Xer                 xer;
Word                gout_reg;
Word                gin_reg;
Word                goe_reg;
Msr                 msr;
Esr                 esr;
Word                srr0, srr1;
Word                csrr0, csrr1;
Word                mcsrr0, mcsrr1;
Word                dear;
Int_ctrl_reg        iccr;

assign reg_file.cr = cr;
assign reg_file.ctr = ctr;
assign reg_file.lnk = lnk;
assign reg_file.xer[31] = xer.so;
assign reg_file.xer[30] = xer.ov;
assign reg_file.xer[29] = xer.ca;
assign reg_file.xer[28:0] = '0;
assign reg_file.gout = gout_reg;
assign reg_file.gin = gin_reg;
assign reg_file.goe = goe_reg;
assign reg_file.srr0 = srr0;
assign reg_file.srr1 = srr1;
assign reg_file.csrr0 = csrr0;
assign reg_file.csrr1 = csrr1;
assign reg_file.mcsrr0 = mcsrr0;
assign reg_file.mcsrr1 = mcsrr1;
assign reg_file.dear = dear;
assign reg_file.iccr = iccr;


/** Connect to external GPR file */
assign
	gpr_file.ra_sel = reg_file.gpr_sel_a,
	gpr_file.rb_sel = reg_file.gpr_sel_b,
	gpr_file.rc_sel = reg_file.gpr_sel_c,
	gpr_file.wa_sel = reg_file.gpr_sel_dest,
	gpr_file.wb_sel = reg_file.gpr_sel_dest_2,
	gpr_file.wa     = reg_file.gpr_dest,
	gpr_file.wb     = reg_file.gpr_dest_2,
	gpr_file.wa_wr  = reg_file.gpr_we,
	gpr_file.wb_wr  = reg_file.gpr_we_2;

assign
	reg_file.gpr_a = gpr_file.ra,
	reg_file.gpr_b = gpr_file.rb,
	reg_file.gpr_c = gpr_file.rc;

/** Some bits in MSR and ESR are set to fixed or undefined values */
always_comb
begin
	reg_file.msr = msr;

	reg_file.msr.comp_mode = 1'b0;  // always in 32bit mode
	reg_file.msr.pr = 1'b0;         // always privileged
	reg_file.msr.fp = 1'b0;         // no floating point
	reg_file.msr.reserved0 = '0;
	reg_file.msr.reserved1 = '0;
	reg_file.msr.reserved2 = '0;
	reg_file.msr.reserved3 = '0;
	reg_file.msr.reserved4 = '0;


	reg_file.esr = esr;

	reg_file.esr.dlk = '0;
	reg_file.esr.reserved0 = '0;
	reg_file.esr.reserved1 = '0;
	reg_file.esr.reserved2 = '0;
	reg_file.esr.reserved3 = '0;
	reg_file.esr.reserved4 = '0;
end

// a non-resettable register file improves performance.
// synchronous reset seems to be just as good.
//always_ff @(posedge clk [>or posedge reset<])
always_ff @(posedge clk or posedge reset)
begin : writer
	if( reset ) begin
		cr  <= '0;
		ctr <= '0;
		lnk <= '0;
		xer <= '0;
	end else begin
		for(int i=0; i<8; i++)
			if( reg_file.wr_cr[i] == 1'b1 ) 
				cr[i] <= reg_file.cr_in;

		if( reg_file.ctr_we ) begin
			ctr <= reg_file.ctr_in;
		end

		if( reg_file.lnk_we ) begin
			lnk <= reg_file.lnk_in;
		end

		if( reg_file.xer_we ) begin
			xer.so <= reg_file.xer_in[31];
			xer.ov <= reg_file.xer_in[30];
			xer.ca <= reg_file.xer_in[29];
		end
	end
end : writer


always_ff @(posedge clk or posedge reset)
begin
	if( reset ) begin
		gout_reg <= '0;
		gin_reg <= '0;
		goe_reg <= '0;
	end else begin
		gin_reg <= reg_file.gin_in;

		if( reg_file.gout_we )
			gout_reg <= reg_file.gout_in;

		if( reg_file.goe_we )
			goe_reg <= reg_file.goe_in;
	end
end


//always_ff @(posedge clk)
always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		msr <= '0;
		esr <= '0;
		srr0 <= '0;
		srr1 <= '0;
		csrr0 <= '0;
		csrr1 <= '0;
		mcsrr0 <= '0;
		mcsrr1 <= '0;
		dear <= '0;
	end else begin
		if( reg_file.msr_pwe )
			msr <= reg_file.msr_pin;
		else if( reg_file.msr_we )
			msr <= reg_file.msr_in;

		// overwrite reserved or unimplemented values
		msr.comp_mode <= 1'b0;  // always in 32bit mode
		msr.pr <= 1'b0;         // always privileged
		msr.fp <= 1'b0;         // no floating point
		msr.reserved0 <= '0;
		msr.reserved1 <= '0;
		msr.reserved2 <= '0;
		msr.reserved3 <= '0;
		msr.reserved4 <= '0;

		if( reg_file.esr_pwe )
			esr <= reg_file.esr_pin;
		else if( reg_file.esr_we )
			esr <= reg_file.esr_in;

		// overwrite reserved values
		esr.dlk <= '0;
		esr.reserved0 <= '0;
		esr.reserved1 <= '0;
		esr.reserved2 <= '0;
		esr.reserved3 <= '0;
		esr.reserved4 <= '0;

		if( reg_file.dear_pwe )
			dear <= reg_file.dear_pin;
		else if( reg_file.dear_we )
			dear <= reg_file.dear_in;

		if( reg_file.srr0_pwe )
			srr0 <= reg_file.srr0_pin;
		else if( reg_file.srr_we )
			srr0 <= reg_file.srr0_in;

		if( reg_file.srr1_pwe )
			srr1 <= reg_file.srr1_pin;
		else if( reg_file.srr_we )
			srr1 <= reg_file.srr1_in;
		
		if( reg_file.csrr0_pwe )
			csrr0 <= reg_file.csrr0_pin;
		else if( reg_file.csrr_we )
			csrr0 <= reg_file.csrr0_in;

		if( reg_file.csrr1_pwe )
			csrr1 <= reg_file.csrr1_pin;
		else if( reg_file.csrr_we )
			csrr1 <= reg_file.csrr1_in;

		if( reg_file.mcsrr0_pwe )
			mcsrr0 <= reg_file.mcsrr0_pin;
		else if( reg_file.mcsrr_we )
			mcsrr0 <= reg_file.mcsrr0_in;

		if( reg_file.mcsrr1_pwe )
			mcsrr1 <= reg_file.mcsrr1_pin;
		else if( reg_file.mcsrr_we )
			mcsrr1 <= reg_file.mcsrr1_in;
	end

always_ff @(posedge clk or posedge reset)
	if( reset )
		iccr <= '0;
	else
		if( reg_file.iccr_we )
			iccr <= reg_file.iccr_in;

//---------------------------------------------------------------------------
// Embedded assertions
//---------------------------------------------------------------------------
// synopsys translate_off

check_write_conflicts: assert property
( @(posedge clk) disable iff (reset) 
 (reg_file.gpr_we == 1'b1 && reg_file.gpr_we_2 == 1'b1) 
  |-> (reg_file.gpr_sel_dest != reg_file.gpr_sel_dest_2) );

// synopsys translate_on

endmodule
