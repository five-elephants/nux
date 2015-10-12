// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Frontend::*;

/** Test the version 2 frontend architecture for a single-thread design. */
module Frontend_test_single();

//---------------------------------------------------------------------------
// Signals
//---------------------------------------------------------------------------

localparam time clk_period = 10ns;

Ram_if #(
	.ADDR_WIDTH($bits(Iaddr)),
	.DATA_WIDTH(32)
) imem();
Register_file_if reg_file();
Wb_channel_if wb_gpr();

logic clk, reset;
logic proc_clk;
logic clk_gate;
Frontend_control ctrl;
Branch_control bctrl;
Issue_slot issue_fxdpt;
Issue_slot issue_branch;
Issue_slot issue_ls;
logic sleeping;



Frontend_single uut(.clk(proc_clk), .*);


Sim_memory #(
	.ADDR_WIDTH($bits(Iaddr)),
	.DATA_WIDTH(32)
) inst_mem (
	.clk, .reset,
	.intf(imem)
);

int cycle;
logic clk_on;


/*Fub_branch fub_branch (
	.clk, .reset,
	.inst(issue_branch),
	.operands(obus),
	.results(rbus_branch)
);*/

//---------------------------------------------------------------------------
always #(clk_period/2) clk = ~clk;
assign proc_clk = clk & clk_gate;
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Test functions
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
function automatic void init_mem_rand();
	for(int i=0; i<2**$bits(Iaddr); i++)
		inst_mem.mem[i] = $urandom;
endfunction
//---------------------------------------------------------------------------
function automatic void init_mem_file(input string filename);
	for(int i=0; i<2**$bits(Iaddr); i++)
		inst_mem.mem[i] = '0;

  $readmemh(filename, inst_mem.mem);
endfunction
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Initial block
//---------------------------------------------------------------------------

initial begin
  cycle = -9999;
	clk = 1'b0;
	reset = 1'b1;
  clk_on = 1'b0;

	//init_mem_rand();
  init_mem_file("test/testcode/load_add_store_code.mem");

	bctrl.jump = 1'b0;
	bctrl.jump_vec = '0;
	bctrl.fb_taken = 1'b0;
	bctrl.fb_not_taken = 1'b0;
	bctrl.fb_pc = '0;

  ctrl.wakeup = 1'b0;
  ctrl.interrupt = 1'b0;

	#(10*clk_period);
	@(negedge clk);
	reset = 1'b0;
  cycle = 0;


  #(100*clk_period);
  bctrl.jump = 1'b1;
  bctrl.jump_vec = $urandom;
  #(clk_period);
  bctrl.jump = 1'b0;
  bctrl.jump_vec = '0;

  /*#(100*clk_period);
  ctrl.wakeup = 1'b1;
  #(clk_period);
  ctrl.wakeup = 1'b0;*/

  #(50*clk_period);
  clk_on = 1'b1;
  #(clk_period);
  ctrl.wakeup = 1'b1;
  ctrl.interrupt = 1'b1;
  bctrl.jump = 1'b1;
  bctrl.jump_vec = '0;
  #(clk_period);
  ctrl.wakeup = 1'b0;
  ctrl.interrupt = 1'b0;
  bctrl.jump = 1'b0;
  bctrl.jump_vec = '0;
  clk_on = 1'b0;

  init_mem_rand();

  #(50*clk_period);
  clk_on = 1'b1;
  #(clk_period);
  ctrl.wakeup = 1'b1;
  ctrl.interrupt = 1'b1;
  bctrl.jump = 1'b1;
  bctrl.jump_vec = '0;
  #(clk_period);
  ctrl.wakeup = 1'b0;
  ctrl.interrupt = 1'b0;
  bctrl.jump = 1'b0;
  bctrl.jump_vec = '0;
  clk_on = 1'b0;

  $display("once more");
  forever begin
    //#($urandom(50)*clk_period);
    #(30*clk_period);

    ctrl.interrupt = 1'b1;
    bctrl.jump = 1'b1;
    bctrl.jump_vec = $urandom;
    #(clk_period);
    ctrl.interrupt = 1'b0;
    bctrl.jump = 1'b0;
    bctrl.jump_vec = '0;

  end
end
//---------------------------------------------------------------------------

always @(posedge clk)
begin
  if( issue_fxdpt.valid ) begin
    $display("[%5d] Issue to fixedpoint: IR: %8h, PC: %08h",
      cycle, issue_fxdpt.ir, issue_fxdpt.pc);
  end
  if( issue_branch.valid ) begin
    $display("[%5d] Issue to     branch: IR: %8h, PC: %08h",
      cycle, issue_branch.ir, issue_branch.pc);
  end
  if( issue_ls.valid ) begin
    $display("[%5d] Issue to load/store: IR: %8h, PC: %08h",
      cycle, issue_ls.ir, issue_ls.pc);
  end

  if( wb_gpr.we ) begin
    $display("[%5d] WB to GPR(%2d) from fu %s",
      cycle, wb_gpr.dest, fu_set_to_string(wb_gpr.src));
  end

  cycle = cycle + 1;
end

assign clk_gate = ~sleeping | clk_on;

//---------------------------------------------------------------------------
property matched_to_memory;
  Pu_inst::Inst i0, i1, i2;
  Pu_types::Address a0, a1, a2;

  @(posedge clk) disable iff(reset)
  ( 
    ( (issue_fxdpt.valid, i0=issue_fxdpt.ir, a0=issue_fxdpt.pc) |-> (i0 === inst_mem.mem[a0]) )
    and ( (issue_branch.valid, i1=issue_branch.ir, a1=issue_branch.pc) |-> (i1 === inst_mem.mem[a1]) )
    and ( (issue_ls.valid, i2=issue_ls.ir, a2=issue_ls.pc) |-> (i2 === inst_mem.mem[a2]) )
  );
endproperty

check_mathech_to_memory: assert property(matched_to_memory);
//---------------------------------------------------------------------------


endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
