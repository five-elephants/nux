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

module Alu_test();

typedef struct packed {
	Word a;
	Word b;
	logic cin;

	Word expected;
	logic ov;
	logic cout;
} Test_vector;

typedef struct packed {
	Word a;
	Word b;
	logic[4:0] rot_dist;
	logic[4:0] rot_start;
	logic[4:0] rot_stop;

	Word expected;
} Test_rotl_vector;

logic clk;
logic reset;

Alu_ctrl_if alu_ctrl();
Alu_result_if alu_res();

Alu uut(
	.clk(clk),
	.reset(reset),
	.ctrl(alu_ctrl),
	.result(alu_res)
);

//-------------------------------------------------------------------------------
task automatic apply_test_vectors(ref Test_vector vecs[]);
	for(int i=0; i < vecs.size(); i++) begin
		//$display("   vector %d", i);
		alu_ctrl.a = vecs[i].a;
		alu_ctrl.b = vecs[i].b;
		alu_ctrl.cin = vecs[i].cin;
		#10 check_vecs: assert( (alu_res.res == vecs[i].expected) 
				&& (alu_res.cout == vecs[i].cout)
				&& (alu_res.ov == vecs[i].ov) )
		else 
			$display("Assertion check_vecs failes on vector no. %d", i);				
	end
endtask
//-------------------------------------------------------------------------------
task test_add;
	Test_vector tvs[]; 
	
	tvs = new [8];
	tvs[0] = '{ a: 32'h0000_0001, b: 32'h0000_0002, cin: '0, 
			expected: 32'h0000_0003, ov: 1'b0, cout: '0 };
	tvs[1] = '{ a: 32'h1000_0001, b: 32'h0000_0002, cin: '0,
			expected: 32'h1000_0003, ov: 1'b0, cout: '0 };
	tvs[2] = '{ a: 32'hffff_ffff, b: 32'h0000_0001, cin: '0,
			expected: 32'h0000_0000, ov: 1'b0, cout: '0 };
	tvs[3] = '{ a: 32'hffff_ffff, b: 32'hffff_ffff, cin: '0,
			expected: 32'hffff_fffe, ov: 1'b0, cout: '1 };
	tvs[4] = '{ a: 32'h7fff_ffff, b: 32'h0000_0001, cin: '0,
			expected: 32'h8000_0000, ov: 1'b1, cout: '0 };
	tvs[5] = '{ a: 32'h8000_0000, b: 32'hffff_ffff, cin: '0,
			expected: 32'h7fff_ffff, ov: 1'b1, cout: '1 };
	tvs[6] = '{ a: 'h1, b: 'h1, cin: '1,
			expected: 'h3, ov: '0, cout: '0 };
	tvs[7] = '{ a: 'h7fff_ffff, b: 'h1, cin: '1,
			expected: 'h8000_0001, ov: '1, cout: '0 };
	

	$display("Checking add");
	alu_ctrl.op = Alu_add;

	apply_test_vectors(tvs);
endtask
//-------------------------------------------------------------------------------
task test_neg;
	Word tv [0:4][0:2] = '{
		// a,            expected,      ov
		'{32'h0000_0000, 32'h0000_0000, 1'b0},
		'{32'h0000_0001, 32'hffff_ffff, 1'b0},
		'{32'h0000_0002, 32'hffff_fffe, 1'b0},
		'{32'hffff_ffff, 32'h0000_0001, 1'b0},
		'{32'h8000_0000, 32'h8000_0000, 1'b1}
	};

	$display("Checking negate");
	alu_ctrl.op = Alu_neg;

	for(int i=$left(tv, 1); 
		i<=$right(tv, 1); 
		i++)
	begin
		$display("   vector %d", i);
		alu_ctrl.a = tv[i][0];
		alu_ctrl.b = '0;
		#10 check_neg: assert( alu_res.res == tv[i][1] );
	end
endtask
//-------------------------------------------------------------------------------
task automatic test_vectors(ref Word vecs[][0:2]);
	for(int i=0; i < vecs.size(); i++) begin
		//$display("   vector %d", i);
		alu_ctrl.a = vecs[i][0];
		alu_ctrl.b = vecs[i][1];
		alu_ctrl.cin = '0;
		#10 check_vecs: assert( alu_res.res == vecs[i][2] );
	end
endtask

task automatic test_vectors_ov(ref Word vecs[][0:3]);
	for(int i=0; i < vecs.size(); i++) begin
		//$display("   vector %d", i);
		alu_ctrl.a = vecs[i][0];
		alu_ctrl.b = vecs[i][1];
		alu_ctrl.cin = '0;
		#10 check_vecs: assert( alu_res.res == vecs[i][2] && alu_res.ov == vecs[i][3][0] );
	end
endtask
//-------------------------------------------------------------------------------
task test_sub;
	Test_vector tv[];

	tv = new [6];
	tv[0] = '{ a: 'h1, b: 'h1, cin: '1, 
			expected: 'h0, ov: '0, cout: '0 };
	tv[1] = '{ a: 'h1, b: 'h4, cin: '1, 
			expected: 'h3, ov: '0, cout: '0 };
	tv[2] = '{ a: 'h1, b: 'h0, cin: '1,
			expected: 'hffff_ffff, ov: '0, cout: '1 };
	tv[3] = '{ a: 'hffff_ffff, b: 'h1, cin: '1,
			expected: 'h2, ov: '0, cout: '0 };
	tv[4] = '{ a: 'h7fff_ffff, b: 'hffff_fffe, cin: '1,
			expected: 'h7fff_ffff, ov: '1, cout: '1 };
	tv[5] = '{ a: 'h1, b: 'h1, cin: '0,
			expected: 'hffff_ffff, ov: '0, cout: '1 };


	$display("Checking subtract");
	alu_ctrl.op = Alu_sub;

	apply_test_vectors(tv);
endtask
//-------------------------------------------------------------------------------
task test_and;
	Word tv[][0:2];

	tv = new [3];
	tv[0] = '{ 'hffff_ffff, 'hffff_ffff, 'hffff_ffff };
	tv[1] = '{ 'hffff_ffff, 'hdead_face, 'hdead_face };
	tv[2] = '{ 'h0000_8000, 'h0000_9000, 'h0000_8000 };
	
	$display("Checking and");
	alu_ctrl.op = Alu_and;
	
	test_vectors(tv);
endtask;
//-------------------------------------------------------------------------------
task test_or;
	Word tv[][0:2];

	tv = new [2];
	tv[0] = '{ 'hffff_0000, 'h0000_ffff, 'hffff_ffff };
	tv[1] = '{ 'h0000_0000, 'hff00_00ff, 'hff00_00ff };

	$display("Checking or");
	alu_ctrl.op = Alu_or;

	test_vectors(tv);
endtask;
//-------------------------------------------------------------------------------
task test_xor;
	Word tv[][0:2];

	tv = new [2];
	tv[0] = '{ 'hffff_0000, 'h0000_ffff, 'hffff_ffff };
	tv[1] = '{ 'hffff_ffff, 'hffff_0000, 'h0000_ffff };

	$display("Checking xor");
	alu_ctrl.op = Alu_xor;

	test_vectors(tv);
endtask;
//-------------------------------------------------------------------------------
task test_nand;
	Word tv[][0:2];

	tv = new [2];
	tv[0] = '{ 'hffff_ffff, 'hffff_0000, 'h0000_ffff };
	tv[1] = '{ 'hffff_0000, 'hffff_0000, 'h0000_ffff };

	$display("Checking nand");
	alu_ctrl.op = Alu_nand;

	test_vectors(tv);
endtask;
//-------------------------------------------------------------------------------
task test_nor;
	Word tv[][0:2];

	tv = new [2];
	tv[0] = '{ 'hffff_ffff, 'hffff_0000, 'h0000_0000 };
	tv[1] = '{ 'h0000_0000, 'h0000_0000, 'hffff_ffff };

	$display("Checking nor");
	alu_ctrl.op = Alu_nor;

	test_vectors(tv);
endtask;
//-------------------------------------------------------------------------------
task test_rotl;
	Test_rotl_vector tvs[];

	tvs = new [5];
	tvs[0] = '{ a: 'b0001, b: '0, rot_dist: 'h1, rot_start: 'h0, rot_stop: 'h1f,
			expected: 'b0010 };
	tvs[1] = '{ a: 'h8000_0000, b: '0, rot_dist: 'h1, rot_start: 'h0, rot_stop: 'h1f,
			expected: 'h0000_0001 };
	tvs[2] = '{ a: 'b1111, b: '0, rot_dist: 'h4, rot_start: 0, rot_stop: 25,
			expected: 'b1100_0000 };
	tvs[3] = '{ a: 'hffff_dead, b: 'h0000_face, rot_dist: 16, rot_start: 0, rot_stop: 15,
			expected: 'hdead_face };
	tvs[4] = '{ a: 'hffff_dead, b: 'h0000_face, rot_dist: 16, rot_start: 0, rot_stop: 31,
			expected: 'hdead_ffff };
	
	$display("Checking rotl");
	alu_ctrl.op = Alu_rotl;

	for(int i=0; i < tvs.size(); i++) begin
		alu_ctrl.a = tvs[i].a;
		alu_ctrl.b = tvs[i].b;
		alu_ctrl.rot_dist = tvs[i].rot_dist;
		alu_ctrl.rot_start = tvs[i].rot_start;
		alu_ctrl.rot_stop = tvs[i].rot_stop;
		#10 check_rotl: assert( (alu_res.res == tvs[i].expected) )
		else 
			$display("Assertion check_rotl failes on vector no. %d", i);				
	end
endtask
//-------------------------------------------------------------------------------
task automatic test_ext_sign_halfword;
	Word tv[][0:2];

	tv = new [3];
	tv[0] = '{ 'hffff, '0, 'hffff_ffff };
	tv[1] = '{ 'h7fff, '0, 'h0000_7fff };
	tv[2] = '{ 'hffff_7fff, '0, 'h0000_7fff };

	$display("Checking extsh");
	alu_ctrl.op = Alu_esh;

	test_vectors(tv);
endtask
//-------------------------------------------------------------------------------
task automatic test_ext_sign_byte;
	Word tv[][0:2];

	tv = new [3];
	tv[0] = '{ 'hff, '0, 'hffff_ffff };
	tv[1] = '{ 'h7f, '0, 'h0000_007f };
	tv[2] = '{ 'hffff_ff7f, '0, 'h0000_007f };

	$display("Checking extsb");
	alu_ctrl.op = Alu_esb;

	test_vectors(tv);
endtask
//-------------------------------------------------------------------------------

always #5ns clk = ~clk;

initial begin
	clk = 1'b0;
	reset = 1'b1;

	alu_ctrl.op = Alu_add;
	alu_ctrl.a = '0;
	alu_ctrl.b = '0;
	alu_ctrl.cin = '0;
	alu_ctrl.en = 1'b0;
	alu_ctrl.rot_dist = '0;
	alu_ctrl.rot_start = '0;
	alu_ctrl.rot_stop = '0;

	#1

	check_reset: assert( alu_res.res == '0 );

	#28ns reset = 1'b0;

	#1ns $display("Checking enable");
	alu_ctrl.op = Alu_add;
	alu_ctrl.a = 32'h0000_0001;
	alu_ctrl.b = 32'h0000_1000;

	// checking ALU features
	alu_ctrl.en = 1'b1;
	#10ns test_add();
	test_neg();
	test_sub();
	test_and();
	test_or();
	test_xor();
	test_nand();
	test_nor();
	test_rotl();
	test_ext_sign_halfword();
	test_ext_sign_byte();

	$display("End of simulation. Stopping now");
	$stop;
end

// --- assertions ---
check_nop: assert property
	(@(posedge clk) disable iff (reset)
		(alu_ctrl.op == Alu_add && alu_ctrl.en == 1'b0) |=> (alu_res.res == '0));

check_enable: assert property
	(@(posedge clk) disable iff (reset)
		(alu_ctrl.en == 'b0) |=> (alu_res.res == '0));

// check negative result flag
check_lt: assert property
	(@(alu_res.res) disable iff (reset)
		(alu_ctrl.en ##1 alu_res.res[$left(alu_res.res)] == 1'b1) 
		|-> (alu_res.lt == 1'b1 && alu_res.gt == 1'b0 && alu_res.eq == 1'b0));

// check equals zero result flag
check_eq: assert property
	(@(alu_res.res) disable iff (reset)
		(alu_res.res == 0)
		|-> (alu_res.eq == 1'b1 && alu_res.lt == 1'b0 && alu_res.gt == 1'b0));

// check positive result flag
check_gt: assert property
	(@(alu_res.res) disable iff (reset)
		(alu_res.res != 0 && alu_res.res[$left(alu_res.res)] == 1'b0) 
		|-> (alu_res.eq == 1'b0 && alu_res.lt == 1'b0 && alu_res.gt == 1'b1));

endmodule
