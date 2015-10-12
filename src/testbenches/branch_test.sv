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


module Branch_test;

//---------------------------------------------------------------------------
class Rand_branch_input;
	// controlpath signals
	rand logic en;
	rand logic jump;
	rand logic dec_ctr;
	rand logic ctr_eq;
	rand logic[4:0] crbi;
	rand logic cond;
	rand logic mask_ctr;
	rand logic mask_cond;

	// datapath signals
	rand Word cr;
	rand Word ctr;

	// random constraints
	constraint ctr_dist {ctr dist {0 :/ 1, 1 :/ 1, [2:2**32-1] :/ 1}; }
	constraint mostly_enabled { en dist {1'b1 := 100, 1'b0 := 0}; }
endclass;
//---------------------------------------------------------------------------

time clk_period = 10ns;
logic clk;
logic reset;


always #(clk_period/2) clk = ~clk;

Rand_branch_input   rin;

Branch_ctrl_if      ctrl();
Branch_data_if      data();
Write_back_data_if  write_back(.clk(clk), .reset(reset));

Branch uut
	(	.clk(clk),
		.reset(reset),
		.ctrl(ctrl),
		.data(data),
		.write_back(write_back) );


initial begin
	rin = new();

	reset = '1;
	clk = '0;

	// reset condition
	ctrl.decode_set_zero();
	
	@(negedge clk);
	#(10*clk_period) reset = '0;

	// test stimulus
	for(int i=0; i<1000; i++) begin
		rin.randomize();

		data.cr = rin.cr;
		data.ctr = rin.ctr;

		ctrl.en = rin.en;
		ctrl.jump = rin.jump;
		ctrl.dec_ctr = rin.dec_ctr;
		ctrl.ctr_eq = rin.ctr_eq;
		ctrl.crbi = rin.crbi;
		ctrl.cond = rin.cond;
		ctrl.mask_ctr = rin.mask_ctr;
		ctrl.mask_cond = rin.mask_cond;

		#clk_period;
	end

	$display(" ==== End of simulation ====");
end


//---------------------------------------------------------------------------
// Assertions
//---------------------------------------------------------------------------

sequence is_unconditional_jump;
	ctrl.en == 1'b1
	&& ctrl.jump == 1'b1;
endsequence;

sequence is_ctr_branch;
	ctrl.en == 1'b1
	&& ctrl.dec_ctr == 1'b1
	&& ctrl.mask_ctr == 1'b0
	&& ctrl.mask_cond == 1'b1;
endsequence;


// check unconditional branch instructions
property unconditional_jump;
	@(posedge clk) disable iff (reset)
		(is_unconditional_jump |=> write_back.jump == 1'b1);
endproperty;

check_unconditional_jump: assert property(unconditional_jump);
cover_unconditional_jump: cover property(unconditional_jump);


// check for correct decrementing of the counter register
property decrement_counter;
	logic[31:0] ctr;

	@(posedge clk) disable iff (reset)
		((ctrl.en == 1'b1 && ctrl.dec_ctr == 1'b1, ctr=data.ctr)
		 |=> write_back.ctr == ctr - 1);
endproperty;

check_decrement_counter: assert property(decrement_counter);
cover_decrement_counter: cover property(decrement_counter);


// check branch on ctr equal zero
property ctr_eq_zero;
	@(posedge clk) disable iff (reset)
		(is_ctr_branch 
		 and data.ctr == 1
		 && ctrl.ctr_eq == 1'b1
		 |=> write_back.jump == 1'b1);
endproperty;
		
check_jump_on_ctr_eq_zero: assert property(ctr_eq_zero);
cover_jump_on_ctr_eq_zero: cover property(ctr_eq_zero);


// check branch on ctr equal zero
property ctr_neq_zero;
	@(posedge clk) disable iff (reset)
		(is_ctr_branch 
		 and data.ctr != 1
		 && ctrl.ctr_eq == 1'b0
		 |=> write_back.jump == 1'b1);
endproperty;
		
check_jump_on_ctr_neq_zero: assert property(ctr_neq_zero);
cover_jump_on_ctr_neq_zero: cover property(ctr_neq_zero);

endmodule

