// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module Tag_shiftreg_test();

localparam time clk_period = 10ns;

// UUT's parameters
localparam int TAG_SIZE = 5;
localparam int DATA_SIZE = 4;
localparam int NUM_STAGES = 3;
localparam int NUM_TESTPORTS = 3;

// UUT's input/output ports
logic clk, reset;
Tag_shiftreg_if 
	#(	.TAG_SIZE(TAG_SIZE),
		.DATA_SIZE(DATA_SIZE),
		.NUM_STAGES(NUM_STAGES),
		.NUM_TESTPORTS(NUM_TESTPORTS) )
	intf();


// UUT instance
Tag_shiftreg 
	#(	.TAG_SIZE(TAG_SIZE),
		.DATA_SIZE(DATA_SIZE),
		.NUM_STAGES(NUM_STAGES),
		.NUM_TESTPORTS(NUM_TESTPORTS) )
	uut(.clk(clk), .reset(reset), .intf(intf));


// clock generation
always begin
	clk = 1'b0;
	#(clk_period/2);
	clk = 1'b1;
	#(clk_period/2);
end

//---------------------------------------------------------------------------
class Random_tag;
	rand logic[TAG_SIZE-1:0]  tag;
	rand logic                tag_valid;
	rand logic[DATA_SIZE-1:0] data;
	rand logic                shift;
	rand bit                  test_from_past[0:NUM_TESTPORTS-1];
	rand int                  test_from_past_index[0:NUM_TESTPORTS-1];
	rand logic[TAG_SIZE-1:0]  rand_test[0:NUM_TESTPORTS-1];
	
	constraint from_past_index { 
		foreach(test_from_past_index[i])
			test_from_past_index[i] inside { [0:NUM_STAGES-1] };
	}

	constraint random_vs_past_ratio {
		foreach(test_from_past[i])
			test_from_past[i] dist { 1'b0 := 3, 1'b1 := 1 };
	}


	logic[TAG_SIZE-1:0]  test[0:NUM_TESTPORTS-1];
	logic[TAG_SIZE-1:0]  past_tags[0:NUM_STAGES-1];

	function void post_randomize();
		past_tags[0] = tag;
		for(int i=1; i<NUM_STAGES; i++)
			past_tags[i] = past_tags[i-1];

		for(int i=0; i<NUM_TESTPORTS; i++) 
			if( test_from_past[i] )
				test[i] = past_tags[test_from_past_index[i]];
			else
				test[i] = rand_test[i];
	endfunction
endclass
//---------------------------------------------------------------------------

// stimulus generation
initial begin
	Random_tag rtag;
	
	rtag = new();

	reset = 1'b1;

	intf.shift = 1'b1;
	intf.tag = '0;
	intf.tag_valid = 1'b0;
	intf.datain = '0;
	for(int k=0; k<NUM_TESTPORTS; k++) intf.test[k] = '0;

	#(100ns);
	@(negedge clk) reset = 1'b0;

	$display("Test 1: Shift always on");
	for(int i=0; i<1000; i++) begin
		rtag.randomize();

		intf.tag = rtag.tag;
		intf.tag_valid = rtag.tag_valid;
		intf.datain = rtag.data;

		for(int j=0; j<NUM_TESTPORTS; j++)
			intf.test[j] = rtag.test[j];

		#(clk_period);
	end

	$display("Test 2: Shift randomly on and off");
	forever begin
		rtag.randomize();

		intf.shift = rtag.shift;
		intf.tag = rtag.tag;
		intf.tag_valid = rtag.tag_valid;
		intf.datain = rtag.data;

		for(int j=0; j<NUM_TESTPORTS; j++)
			intf.test[j] = rtag.test[j];

		#(clk_period);
	end
end

endmodule
