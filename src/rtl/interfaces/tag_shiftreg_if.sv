// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Tag_shiftreg_if
	#(	/** Number of bits for each tag */
		parameter int TAG_SIZE = 5,

		/** Number of bits for data associated with tag */
		parameter int DATA_SIZE = 0,

		/** Number of register stages in the shift register */
		parameter int NUM_STAGES = 3,

		/** Number of test tags that can be simultaneously presented */
		parameter int NUM_TESTPORTS = 3 );

	logic                shift;

	logic[TAG_SIZE-1:0]  tag;
	logic                tag_valid;
	logic[DATA_SIZE-1:0] datain;
	logic[TAG_SIZE-1:0]  test[0:NUM_TESTPORTS-1];

	logic                found[0:NUM_TESTPORTS-1];
	logic                index[0:NUM_TESTPORTS-1][0:NUM_STAGES-1];
	logic[DATA_SIZE-1:0] dataout[0:NUM_TESTPORTS-1];


	modport user
		(	output shift, tag, tag_valid, datain, test, 
			input found, index, dataout );
	modport internal
		(	input shift, tag, tag_valid, datain, test,
			output found, index, dataout );
endinterface
