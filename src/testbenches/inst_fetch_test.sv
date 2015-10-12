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
import Pu_inst::*;


module Inst_fetch_test;

time clk_period = 10ns;
logic clk;
logic reset;

Inst_fetch_ctrl_if    ctrl();
Decode_data_if  decode();
Ram_if #(.ADDR_WIDTH(10)) imem_if();

L1_memory #(	.ADDR_WIDTH(10) ) imem
	(	.clk(clk),
		.reset(reset),
		.intf(imem_if) );

Inst_fetch uut
	(	.clk(clk),
		.reset(reset),
		.ctrl(ctrl),
		.decode(decode),
		.imem(imem_if) );

always #(clk_period/2) clk = ~clk;

initial begin
	$readmemh("test/imem_empty.mem", imem.mem);

	for(int i=0; i<1024; ++i) begin
		imem.mem[i] = i;
	end

	reset = '1;
	clk = '0;

	ctrl.new_pc = '0;
	ctrl.jump = '0;
	ctrl.hold_decode = '0;
	ctrl.hold_data = '0;

	#(3*clk_period) reset = '0;

	check_reset: assert( decode.pc == '0 && 
			(decode.inst.d.opcd == Op_ori
			 && decode.inst.d.rt == '0
			 && decode.inst.d.ra == '0
			 && decode.inst.d.d == '0) );

	@(negedge clk);
	#(10*clk_period) ctrl.hold_data = '1;
	#(10*clk_period);

	ctrl.hold_data = '0;
	ctrl.jump = '1;
	ctrl.new_pc = 286;
	#clk_period ctrl.jump = '0;
	ctrl.new_pc = '0;
	#(10*clk_period);

	ctrl.hold_data = '1;
	#(10*clk_period) ctrl.jump = '1;
	ctrl.new_pc = 61;
	#(clk_period) ctrl.jump = '0;
	ctrl.new_pc = 0;

	#(10*clk_period) ctrl.hold_data = '0;
	

end


// --- assertions ---

property count_up;
	Address pc;

	@(posedge clk) disable iff (reset)
		(reset == '0 ##1 
		 	ctrl.jump == '0 && ctrl.hold == '0, 
			pc = decode.pc)
		|=> (decode.pc == pc+1);
endproperty

check_counting: assert property(count_up);
cover_counting: cover property(count_up);


property hold;
	Address pc;
	Inst inst;

	@(posedge clk) disable iff (reset)
		(reset == '0 ##1
		 	ctrl.jump == '0 && ctrl.hold == '1,
			pc = decode.pc, inst = decode.inst)
		|=> (decode.pc == pc && decode.inst == inst);
endproperty

check_hold: assert property(hold);
cover_hold: cover property(hold);


property jump;
	Address new_pc;

	@(posedge clk) disable iff (reset)
		(reset == '0 ##1
		 	ctrl.jump == '1 && ctrl.hold == '0,
			new_pc = ctrl.new_pc)
		|=> (decode.pc == new_pc);
endproperty

check_jump: assert property(jump);
cover_jump: cover property(jump);


property jump_and_hold;
	Address new_pc;

	@(posedge clk) disable iff (reset)
		(reset == '0 ##1
		 	ctrl.jump == '1 && ctrl.hold == '1,
			new_pc = ctrl.new_pc)
		|=> (decode.pc == new_pc);
endproperty

check_jump_and_hold: assert property(jump_and_hold);
cover_jump_and_hold: cover property(jump_and_hold);

endmodule
