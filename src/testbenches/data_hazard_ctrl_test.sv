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

module Data_hazard_ctrl_test();

time clk_period = 10ns;
logic clk;
logic reset;

Data_hazard_ctrl_if   ctrl();
Inst_fetch_ctrl_if    if_ctrl();

Data_hazard_ctrl      uut(.*);


always #(clk_period/2) clk = ~clk;

//---------------------------------------------------------------------------
class Reg_access;
	virtual interface Data_hazard_ctrl_if ctrl = null;

	rand Reg_index gpr;
	rand bit gpr_ab;
	rand bit use_gpr;

	rand bit use_cr;
	rand int sel_cr;
	constraint sel_cr_bounds { sel_cr inside {[0:7]}; }

	rand bit use_ctrlnk;  // '1 : use ctr, '0 : use lnk

	function new(virtual interface Data_hazard_ctrl_if c);
		ctrl = c;
	endfunction

	task automatic read();
		if( use_gpr ) begin
			if( gpr_ab ) begin
				ctrl.gpr_a = gpr;
				ctrl.read_gpr_a = 1'b1;
			end else begin
				ctrl.gpr_b = gpr;
				ctrl.read_gpr_b = 1'b1;
			end
		end

		if( use_cr )
			ctrl.read_cr[sel_cr] = 1'b1;

		if( use_ctrlnk )
			ctrl.read_ctr = 1'b1;
		else
			ctrl.read_lnk = 1'b1;
	endtask

	task automatic write();
		if( use_gpr ) begin
			ctrl.gpr_dest = gpr;
			ctrl.write_gpr_dest = 1'b1;
		end

		if( use_cr )
			ctrl.write_cr[sel_cr] = 1'b1;

		if( use_ctrlnk )
			ctrl.write_ctr = 1'b1;
		else
			ctrl.write_lnk = 1'b1;
	endtask

	task automatic neutralize();
		ctrl.read_gpr_a = 1'b0;
		ctrl.read_gpr_b = 1'b0;
		ctrl.write_gpr_dest = 1'b0;
		ctrl.read_cr = '0;
		ctrl.write_cr = '0;
		ctrl.read_ctr = '0;
		ctrl.write_ctr = '0;
		ctrl.read_lnk = '0;
		ctrl.write_lnk = '0;
	endtask

endclass : Reg_access
//---------------------------------------------------------------------------
class Reg_access_seq;
	virtual interface Data_hazard_ctrl_if ctrl = null;

	rand Reg_access acc;
	rand int interval;
	constraint interval_bounds { interval inside {[0:6]}; }


	function new(virtual interface Data_hazard_ctrl_if c);
		ctrl = c;
		acc = new(c);
	endfunction


	task automatic read_after_write();
		acc.neutralize();
		acc.write();

		for(int i=0; i<interval; ++i) begin
			#(clk_period);
			acc.neutralize();
		end

		acc.read();
		#(clk_period);
	endtask

	task automatic write_after_read();
	endtask

	task automatic write_after_write();
	endtask

endclass : Reg_access_seq
//---------------------------------------------------------------------------

Reg_access_seq acc_seq;

initial begin
	acc_seq = new (ctrl);

	reset = 1'b1;
	clk = 1'b0;

	// reset state
	ctrl.gpr_a = '0;
	ctrl.gpr_b = '0;
	ctrl.gpr_dest = '0;
	ctrl.read_gpr_a = '0;
	ctrl.read_gpr_b = '0;
	ctrl.write_gpr_dest = '0;
	ctrl.read_cr = '0;
	ctrl.write_cr = '0;
	ctrl.read_ctr = '0;
	ctrl.write_ctr = '0;
	ctrl.read_lnk = '0;
	ctrl.write_lnk = '0;

	@(negedge clk);
	#(10*clk_period) reset = 1'b0;

	$display("Testing read after write register accesses");
	for(int i=0; i<1000; ++i) begin
		acc_seq.randomize();
		acc_seq.read_after_write();
	end

	$display("Data_hazard_ctrl_test done.");
end



//---------------------------------------------------------------------------
// Assertions
//---------------------------------------------------------------------------

// match read access to GPR one to three clock cycles after a write access to
// the same GPR.
sequence gpr_raw;
	Reg_index gpr;

	(ctrl.write_gpr_dest == 1'b1 && ctrl.gpr_dest != '0, gpr = ctrl.gpr_dest)
		## [1:3] ((ctrl.gpr_a == gpr && ctrl.read_gpr_a) 
				|| (ctrl.gpr_b == gpr && ctrl.read_gpr_b));
endsequence

// match read after write accesses for condition register
sequence cr_raw;
	logic[0:7] cr;

	(ctrl.write_cr != '0, cr = ctrl.write_cr)
		## [1:3] (ctrl.read_cr & cr);
endsequence

sequence ctr_raw;
	ctrl.write_ctr ##[1:3] ctrl.read_ctr;
endsequence

sequence lnk_raw;
	ctrl.write_lnk ##[1:3] ctrl.read_lnk;
endsequence

sequence read_after_write;
	gpr_raw or cr_raw or ctr_raw or lnk_raw;
endsequence

// in case of read after write access, the read must be stalled
property stall_read_after_write;
	Reg_index gpr;
	@(posedge clk) disable iff(reset)
		(read_after_write |-> if_ctrl.hold == 1'b1);
endproperty

check_stall_read_after_write: assert property(stall_read_after_write);
cover_stall_read_after_write: cover property(stall_read_after_write);


// count how often the individual registers are written
count_gpr_writes: cover property
	( @(posedge clk) disable iff(reset)
	  	(ctrl.write_gpr_dest));

count_cr_writes: cover property
	( @(posedge clk) disable iff(reset)
	  	(ctrl.write_cr != '0) );

count_ctr_writes: cover property
	( @(posedge clk) disable iff(reset)
	  	(ctrl.write_ctr) );

count_lnk_writes: cover property
	( @(posedge clk) disable iff(reset)
	  	(ctrl.write_lnk) );


endmodule

