// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Timer_unit
	(	input logic clk, reset,
		Timer_if.timer  intf );

import Pu_types::*;


//---------------------------------------------------------------------------
// Local signals
//---------------------------------------------------------------------------

Tcr        tcr;
Tsr        tsr;
Timer      tbu, tbl;
Timer      dec, decar;

Tcr        next_tcr;
Tsr        next_tsr;
Timer      next_tbu, next_tbl;
Timer      next_dec, next_decar;

logic[4:0] fit_bit;

//---------------------------------------------------------------------------

assign
	intf.tcr = tcr,
	intf.tsr = tsr,
	intf.tbu = tbu,
	intf.tbl = tbl,
	intf.dec = dec,
	intf.decar = decar;


always_comb begin
	// default assignment
	next_decar = decar;
	next_tcr = tcr;
	next_tsr = tsr;

	// timer increment/decrement
	{next_tbu, next_tbl} = {tbu, tbl} + 1;


	if( dec == 1 ) begin
		next_tsr.dis = 1'b1;

		if( tcr.are )
		//if( intf.get_are() )
			next_dec = decar;
		else
			next_dec = 0;
	end else if( dec == 0 )
		next_dec = 0;
	else
		next_dec = dec - 1;

	// write access
	if( intf.tbu_we )
		next_tbu = intf.tbu_in;

	if( intf.tbl_we )
		next_tbl = intf.tbl_in;

	if( intf.dec_we )
		next_dec = intf.dec_in;

	if( intf.decar_we )
		next_decar = intf.decar_in;

	if( intf.tcr_we )
		next_tcr = intf.tcr_in;

	if( intf.tsr_we ) begin
		// TSR is not directly written. the input is a mask to clear the register
		next_tsr = tsr & ~intf.tsr_in;
	end

	// the exception can also be caused by a write
	if( (next_tbl[fit_bit] == 1'b1) && (tbl[fit_bit] == 1'b0) )
		next_tsr.fis = 1'b1;
end


always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		tbu <= '0;
		tbl <= '0;
		dec <= '0;
		decar <= '0;
		tsr <= '0;
		tcr <= '0;
	end else begin
		tbu <= next_tbu;
		tbl <= next_tbl;
		dec <= next_dec;
		decar <= next_decar;
		tsr <= next_tsr;
		tcr <= next_tcr;
	end

//---------------------------------------------------------------------------
// Fixed interval timer
//---------------------------------------------------------------------------


always_comb begin
	unique case(tcr.fp)
		2'b00:   fit_bit <= 5'd08;
		2'b01:   fit_bit <= 5'd12;
		2'b10:   fit_bit <= 5'd16;
		2'b11:   fit_bit <= 5'd20;
		default: fit_bit <= 'x;
	endcase
end


endmodule
