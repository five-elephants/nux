// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Gpr_file 
	#(	parameter bit SINGLE_WRITE_PORT = 1'b0 )
	(	input logic clk, reset,
		Gpr_file_if.gpr_file  intf );

import Pu_types::*;


Word  gpr[0:31];

//---------------------------------------------------------------------------
//function automatic void read_port(
	//input Reg_index sel,
	//output Word val );

	//if( intf.wa_wr && (intf.wa_sel == sel) )
		//val = intf.wa;
	//else if( (SINGLE_WRITE_PORT == 1'b0)
		//&& (intf.wb_wr && (intf.wb_sel == sel)) )
		//val = intf.wb;
	//else
		//val = gpr[sel];
//endfunction
function automatic void read_port(
	input Reg_index sel,
	output Word val );

	if( intf.wa_wr && (intf.wa_sel == sel) )
		val = intf.wa;
	else
		val = gpr[sel];
endfunction
//---------------------------------------------------------------------------


/** Synchronous read-out of GPRs */
Reg_index intf_ra_sel, intf_rb_sel, intf_rc_sel;
Word intf_ra, intf_rb, intf_rc;

always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		intf_ra_sel <= '0;
		intf_rb_sel <= '0;
		intf_rc_sel <= '0;
	end else begin
		intf_ra_sel <= intf.ra_sel;
		intf_rb_sel <= intf.rb_sel;
		intf_rc_sel <= intf.rc_sel;
	end

always_comb
//always @(intf.ra_sel, 
	//intf.rb_sel,
	//intf.rc_sel,
	//intf.wa_sel,
	//intf.wb_sel,
	//intf.wa_wr,
	//intf.wb_wr,
	//intf.wa,
	//intf.wb,
	//gpr[intf.ra_sel],
	//gpr[intf.rb_sel],
	//gpr[intf.rc_sel])
begin
	read_port(intf_ra_sel, intf_ra);
	read_port(intf_rb_sel, intf_rb);
	read_port(intf_rc_sel, intf_rc);
end

assign
	intf.ra = intf_ra,
	intf.rb = intf_rb,
	intf.rc = intf_rc;

/*always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		intf.ra <= '0;
		intf.rb <= '0;
		intf.rc <= '0;
	end else begin
		intf.ra <= intf_ra;
		intf.rb <= intf_rb;
		intf.rc <= intf_rc;
	end*/


/** Synchronous write with synchronous reset of GPRs */
always_ff @(posedge clk)
//always_ff @(posedge clk or posedge reset)
	if( reset ) begin     // removing reset makes the gpr_file a good deal smaller
		for(int i=0; i<32; i++)
			gpr[i] <= '0;
	end else begin
		if( intf.wa_wr )
			gpr[intf.wa_sel] <= intf.wa;
		
		//if( SINGLE_WRITE_PORT == 1'b0 ) begin
			//if( intf.wb_wr )
				//gpr[intf.wb_sel] <= intf.wb;
		//end
	end

//---------------------------------------------------------------------------
// synopsys translate_off
initial begin
	static_check_one_write_port: assert(SINGLE_WRITE_PORT == 1'b1) 
		else $error("This implementation only supports one write port.");
end
// synopsys translate_on
//---------------------------------------------------------------------------

endmodule
