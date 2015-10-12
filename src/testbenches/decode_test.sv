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


module Decode_test;

/** Generator for instructions to use with directed random testing.
 * */
class Instruction_rand;
	rand Opcd opcd;
	rand logic[5:0] ra;
	rand logic[5:0] rb;
	rand logic[5:0] rt;
	rand logic[15:0] d;

	rand logic hold;
	constraint seldom_hold { hold dist {1'b0 := 10, 1'b1 := 1}; }

	function automatic Inst d_form;
		d_form.d.opcd = opcd;
		d_form.d.ra = ra;
		d_form.d.rt = rt;
		d_form.d.d = d;
	endfunction
		
endclass


time clk_period = 10ns;
logic clk;
logic reset;
Instruction_rand rand_inst;  // variable for random coverage of instructions



always #(clk_period/2) clk = ~clk;

Decode_ctrl_if         ctrl();
Inst_fetch_ctrl_if     ctrl_inst_fetch();
Alu_ctrl_if            ctrl_alu();
Branch_ctrl_if         ctrl_branch();
Load_store_ctrl_if     ctrl_load_store(.clk(clk), .reset(reset));
Write_back_ctrl_if     ctrl_write_back(.clk(clk), .reset(reset));
Data_hazard_ctrl_if    ctrl_data_hazard();
Branch_hazard_ctrl_if  ctrl_branch_hazard();
Decode_data_if         data();
Alu_data_if            alu();
Branch_data_if         branch();
Load_store_data_if     load_store(.clk(clk), .reset(reset));
Register_file_if       register_file();

Decode uut
	(	.clk(clk),
		.reset(reset),
		.ctrl(ctrl),
		.ctrl_inst_fetch(ctrl_inst_fetch),
		.ctrl_alu(ctrl_alu),
		.ctrl_branch(ctrl_branch),
		.ctrl_load_store(ctrl_load_store),
		.ctrl_write_back(ctrl_write_back),
		.ctrl_data_hazard(ctrl_data_hazard),
		.ctrl_branch_hazard(ctrl_branch_hazard),
		.data(data),
		.alu(alu),
		.branch(branch),
		.load_store(load_store),
		.register_file(register_file) );


initial begin
	rand_inst = new;

	reset = '1;
	clk = '0;

	data.pc = '0;
	data.inst.d.opcd = Op_ori;  // nop
	data.inst.d.rt = '0;
	data.inst.d.ra = '0;
	data.inst.d.d = '0;

	register_file.gpr_a = '0;
	register_file.gpr_b = '0;
	register_file.gpr_rs = '0;
	register_file.cr = '0;
	register_file.ctr = '0;
	register_file.lnk = '0;

	@(negedge clk);
	#(10*clk_period) reset = '0;

	check_reset_inst_fetch: assert(ctrl_inst_fetch.hold_decode == '0);

	check_reset_alu: assert(ctrl_alu.en == '0
							 && ctrl_alu.op == Alu_or
							 && ctrl_alu.rot_dist == '0
							 && ctrl_alu.rot_start == '0
							 && ctrl_alu.rot_stop == '0);

	check_reset_branch: assert(ctrl_branch.en == '0
								&& ctrl_branch.jump == '0
								&& ctrl_branch.dec_ctr == '0
								&& ctrl_branch.ctr_eq == '0
								&& ctrl_branch.crbi == '0
								&& ctrl_branch.cond == '0
								&& ctrl_branch.mask_ctr == '0
								&& ctrl_branch.mask_cond == '0);

	check_reset_load_store: assert(ctrl_load_store.we == '0);

	check_reset_write_back: assert(ctrl_write_back.gpr_dest == '0
									&& ctrl_write_back.gpr_we == '0
									&& ctrl_write_back.use_alu == '0
									&& ctrl_write_back.record_cr == '0);

	// TODO Data_hazard_ctrl_if
	// TODO Control_hazard_ctrl_if

	// nop
	#(clk_period);

	#(clk_period);
	data.inst.d.opcd = Op_ori;
	data.inst.d.rt = 5'b00001;
	data.inst.d.ra = 5'b00010;
	data.inst.d.d = 16'hffff;

	#(clk_period);
	data.inst.d.opcd = Op_addi;
	data.inst.d.rt = 5'b00001;
	data.inst.d.ra = 5'b00010;
	data.inst.d.d  = 16'hffff;

	#(clk_period);
	for(int i=0; i<100; ++i) begin
		rand_inst.randomize();
		#(clk_period) data.inst = rand_inst.d_form();
	end

	$display(" ==== End of simulation ==== ");
	
end


// --- assertions ---

sequence is_alu_operation;
	data.inst.d.opcd == Op_subfic
	|| data.inst.d.opcd == Op_addic
	|| data.inst.d.opcd == Op_addic_rec
	|| data.inst.d.opcd == Op_addi
	|| data.inst.d.opcd == Op_addis
	|| data.inst.d.opcd == Op_ori
	|| data.inst.d.opcd == Op_alu_xo;
endsequence

sequence is_branch_operation;
	data.inst.d.opcd == Op_branch
	|| data.inst.d.opcd == Op_bc
	|| data.inst.d.opcd == Op_bclr;
endsequence

sequence is_load_operation;
	data.inst.d.opcd == Op_lwz;
endsequence

sequence is_store_operation;
	data.inst.d.opcd == Op_stw;
endsequence

sequence not_is_nop;
	data.inst.d.opcd != Op_ori
	|| data.inst.d.rt != '0
	|| data.inst.d.ra != '0
	|| data.inst.d.d != '0;
endsequence

sequence is_nop;
	data.inst.d.opcd == Op_ori
	&& data.inst.d.rt == '0
	&& data.inst.d.ra == '0
	&& data.inst.d.d == '0;
endsequence

sequence reset_inst_fetch;
	ctrl_inst_fetch.hold_decode  == '0;
endsequence

sequence reset_alu;
	ctrl_alu.en == '0
	 && ctrl_alu.op == Alu_or
	 && ctrl_alu.rot_dist == '0
	 && ctrl_alu.rot_start == '0
	 && ctrl_alu.rot_stop == '0;
endsequence

sequence reset_branch;
	ctrl_branch.en == '0
	 && ctrl_branch.jump == '0
	 && ctrl_branch.dec_ctr == '0
	 && ctrl_branch.ctr_eq == '0
	 && ctrl_branch.crbi == '0
	 && ctrl_branch.cond == '0
	 && ctrl_branch.mask_ctr == '0
	 && ctrl_branch.mask_cond == '0;
endsequence

sequence reset_load_store;
	ctrl_load_store.we == '0;
endsequence

sequence reset_write_back;
	ctrl_write_back.gpr_dest == '0
	 && ctrl_write_back.gpr_we == '0
	 && ctrl_write_back.use_alu == '0
	 && ctrl_write_back.record_cr == '0;
endsequence

// check enable signals for ALU operations
property alu_op_enables;
	@(posedge clk) disable iff (reset)
		((is_alu_operation and not_is_nop)
		 |=> ctrl_alu.en == '1 && ctrl_branch.en == '0);
endproperty

check_alu_op_enables: assert property(alu_op_enables);
cover_alu_op_enables: cover property(alu_op_enables);


// check enable signals for branch operations
property branch_op_enables;
	@(posedge clk) disable iff (reset)
		(is_branch_operation
		 |=> ctrl_branch.en == '1);
endproperty

check_branch_op_enables: assert property(branch_op_enables);
cover_branch_op_enables: cover property(branch_op_enables);


// disable for low-power consumption, when instruction is nop
property nop_disable;
	@(posedge clk) disable iff (reset)
		(is_nop 
		 |=> ctrl_alu.en == '0 && ctrl_branch.en == '0);
endproperty

check_nop_disable: assert property(nop_disable);
cover_nop_disable: cover property(nop_disable);

// check selection of register operands from instruction word
property select_reg; // TODO check must be opcode dependend
	logic[4:0] rt;
	logic[4:0] ra;
	logic[4:0] rb;

	@(posedge clk) disable iff (reset)
		((data.inst.xo.opcd != Op_ori, 
		  rt = data.inst.xo.rt, ra = data.inst.xo.ra, rb = data.inst.xo.rb)
		 |-> (register_file.gpr_sel_a == ra
			 && register_file.gpr_sel_b == rb ));
endproperty

check_select_reg: assert property(select_reg);
cover_select_reg: cover property(select_reg);


// check add
property inst_add;
	@(posedge clk) disable iff (reset)
		((data.inst.d.opcd == Op_addic
		 	|| data.inst.d.opcd == Op_addic_rec
			|| data.inst.d.opcd == Op_addi
			|| data.inst.d.opcd == Op_addis)
		|=> (ctrl_alu.en == '1 && ctrl_alu.op == Alu_add)
		and reset_inst_fetch
		and reset_branch
		and reset_load_store);
endproperty

check_inst_add: assert property(inst_add);
cover_inst_add: cover property(inst_add);


// check branch (unconditional)
property inst_branch;
	logic[23:0] li;

	@(posedge clk) disable iff (reset)
		((data.inst.d.opcd == Op_branch, li = data.inst.i.li)
		 |=> (ctrl_branch.en == '1 
			 && ctrl_alu.en == '1
			 && ctrl_branch.jump == '1
			 && alu.a == {{8{li[23]}}, li[23:0]})
		 and reset_inst_fetch
		 and reset_load_store);
endproperty

check_inst_branch: assert property(inst_branch);
cover_inst_branch: cover property(inst_branch);

// check branch (conditional)
property inst_bc;
	logic[13:0] bd;
	logic[4:0]  bo;
	logic[4:0]  bi;

	@(posedge clk) disable iff (reset)
		((data.inst.d.opcd == Op_bc, 
		  	bd = data.inst.b.bd,
			bo = data.inst.b.bo,
			bi = data.inst.b.bi)
		 |=> (ctrl_branch.en == '1
			 && ctrl_alu.en == '1
			 && alu.a == {{18{bd[13]}}, bd[13:0]}
			 && ctrl_branch.crbi == bi
			 && ctrl_branch.cond == bo[3]
			 && ctrl_branch.mask_cond == bo[4]
			 && ctrl_branch.ctr_eq == bo[1]
			 && ctrl_branch.mask_ctr == bo[2]
			 && ctrl_branch.dec_ctr == ~bo[2])
		 and reset_inst_fetch
		 and reset_load_store);
endproperty

check_inst_bc: assert property(inst_bc);
cover_inst_bc: cover property(inst_bc);


// check load instruction


endmodule

