// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Decode
	#(	parameter bit OPT_GPR_ONE_WRITE_PORT = 1'b0,
		parameter bit WITH_MULTIPLIER = 1'b1,
		parameter bit WITH_DIVIDER = 1'b1)
	(	input logic clk,
		input logic reset,

		// own control interface
		Decode_ctrl_if.decode         ctrl,

		// control interfaces of other modules
		Inst_fetch_ctrl_if.decode     ctrl_inst_fetch,
		//Alu_ctrl_if.decode            ctrl_alu,
		Fixedpoint_ctrl_if            ctrl_fixedpoint,
		Branch_ctrl_if.decode         ctrl_branch,
		Trap_ctrl_if.decode           ctrl_trap,
		Load_store_ctrl_if.decode     ctrl_load_store,
		Write_back_ctrl_if.decode     ctrl_write_back,
		Data_hazard_ctrl_if           ctrl_data_hazard,

		// data interfaces
		Decode_data_if.decode         data,
		//Alu_data_if.decode            alu,
		Fixedpoint_data_if.op_fetch   fixedpoint,
		Branch_data_if.decode         branch,
		Trap_data_if.decode           trap,
		Load_store_data_if.decode     load_store,
		Write_back_data_if.decode     write_back,
		
		Register_file_if.read         register_file,
		Timer_if.pu                   timer,
		Int_sched_if.decode           int_sched );

import Pu_types::*;

localparam NUM_SUBMODULES = 3 + ((WITH_MULTIPLIER || WITH_DIVIDER) ? 1 : 0);
Control_word[0:NUM_SUBMODULES-1] cws;
	
// parallel decoder modules
Decode_single dec_single
	(	.clk(clk),
		.reset(reset),
		.ctrl(ctrl),
		.data(data),
		.register_file(register_file),
		.cw(cws[0]) );

Dec_load_update 
	#( 	.MULTIPHASE(OPT_GPR_ONE_WRITE_PORT) )
	dec_load_update
	(	.clk(clk),
		.reset(reset),
		.ctrl(ctrl),
		.data(data),
		.cw(cws[1]) );

Dec_mem_multiple dec_mem_multiple
	(	.clk(clk),
		.reset(reset),
		.ctrl(ctrl),
		.data(data),
		.cw(cws[2]) 
	);

generate if( WITH_MULTIPLIER || WITH_DIVIDER ) begin : gen_mul_control
	Dec_mul_div dec_mul_div
		(	.clk(clk),
			.reset(reset),
			.ctrl(ctrl),
			.data(data),
			.fxdp_fb(ctrl_fixedpoint.feedback),
			.cw(cws[3]) );
			
	// synopsys translate_off
	check_one_active_with_mul: assert property
	( @(posedge clk) disable iff(reset)
		$onehot({dec_single.active, dec_load_update.active, dec_mem_multiple.active, dec_mul_div.active}) );
	// synopsys translate_on
end	else begin
	// synopsys translate_off
	check_one_active_without_mul: assert property
	( @(posedge clk) disable iff(reset)
		$onehot({dec_single.active, dec_load_update.active, dec_mem_multiple.active}) );
	// synopsys translate_on
end
endgenerate

// control signal reduction stage
Control_reduce #(.NUM_INPUTS(NUM_SUBMODULES)) 
	reduce	
	(	.clk(clk),
		.reset(reset),
		.cws(cws),
		.ctrl(ctrl),
		.inst_fetch(ctrl_inst_fetch),
		//.alu(ctrl_alu),
		.fixedpoint(ctrl_fixedpoint),
		.branch(ctrl_branch),
		.trap(ctrl_trap),
		.load_store(ctrl_load_store),
		.write_back(ctrl_write_back),
		.data_hazard(ctrl_data_hazard.decode),
		.register_file(register_file),
		.int_sched(int_sched)
	);

//
// datapath assignments
//

Operand_fetch  op_fetch(.*, .data_hazard(ctrl_data_hazard.operand_fetch));


endmodule

