// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** This module is a shift register for tags with additional compare logic to
* detect wether a given tag is present in the shift register. */
// TODO there should be an option to disable source logic for the index signal
module Tag_shiftreg
	#(	/** Number of bits for each tag */
		parameter int TAG_SIZE = 5,

		/** Number of bits for data associated with tag */
		parameter int DATA_SIZE = 0,

		/** Number of register stages in the shift register */
		parameter int NUM_STAGES = 3,

		/** Number of test tags that can be simultaneously presented */
		parameter int NUM_TESTPORTS = 3 )

	(	input logic                   clk, reset,
		input logic                   shift,

		input logic[TAG_SIZE-1:0]     tag,
		input logic                   tag_valid,
		input logic[DATA_SIZE-1:0]    datain,
		input logic[TAG_SIZE-1:0]     test[0:NUM_TESTPORTS-1],

		output logic                  found[0:NUM_TESTPORTS-1],
		output logic                  index[0:NUM_TESTPORTS-1][0:NUM_STAGES-1],
		output logic[DATA_SIZE-1:0]   dataout[0:NUM_TESTPORTS-1] );

// internal types
typedef logic[TAG_SIZE-1:0] Tag;
typedef logic[DATA_SIZE-1:0] Data;

// internal signals
Tag    tags[0:NUM_STAGES-1];
logic  valids[0:NUM_STAGES-1];
Data   data[0:NUM_STAGES-1];

Data   dataout_i[0:NUM_TESTPORTS-1];

//---------------------------------------------------------------------------
/** Shift register process */
always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		for(int i=0; i<NUM_STAGES; i++) begin
			tags[i] <= '0;
			valids[i] <= 1'b0;
			data[i] <= '0;
		end
	end else begin
		if( shift ) begin
			tags[0] <= tag;
			valids[0] <= tag_valid;
			data[0] <= datain;

			for(int i=1; i<NUM_STAGES; i++) begin
				tags[i] <= tags[i-1];
				valids[i] <= valids[i-1];
				data[i] <= data[i-1];
			end
		end
	end
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
/** Compare logic */
generate
	genvar i;
	genvar j;
	for(i=0; i<NUM_TESTPORTS; i++) begin : g_testport
		logic cmp[0:NUM_STAGES-1];

		for(j=0; j<NUM_STAGES; j++) begin : g_stage_cmp
			assign cmp[j] = (& (~(test[i] ^ tags[j])) );
		end : g_stage_cmp
		

		always_comb begin
			// default assignments
			found[i] = 1'b0;
			for(int k=0; k<NUM_STAGES; k++) begin
				index[i][k] = 1'b0;
				dataout_i[i] = '0;
			end


			for(int k=0; k<NUM_STAGES; k++)
				if( cmp[k] && valids[k] ) begin
					found[i] = 1'b1;
					index[i][k] = 1'b1;
					dataout_i[i] = data[k];
					break;  // select the first match found
				end
		end

		if( DATA_SIZE != 0 )
			assign dataout[i] = dataout_i[i];
		else
			assign dataout[i] = '0;

		//---------------------------------------------------------------------------
		// synopsys translate_off
		/** A tag that is presented to the module when shift is asserted should be 
		* found, when the same tag is presented to a testport up to NUM_STAGES-1 
		* cycles later. */
		property tags_are_found;
			Tag t;

			@(posedge clk) disable iff(reset)
				((tag_valid && shift, t = tag) 
				##1 (shift [= 0:NUM_STAGES-1])  // non-consecutive repetition operator :)
				##1 (test[i] == t)
				|-> (found[i] == 1'b1));
		endproperty;

		/** Along with asserting found, the associated data is to be returned. The 
		* property also checks, that only the most recent data value is returned should
		* the tag be present multiple times. */
		property data_is_returned;
			Tag t;
			Data d;

			@(posedge clk) disable iff(reset)
				(( (DATA_SIZE!=0) && tag_valid && shift, 
					t = tag,
					d = datain ) 
				##1 ((tag != t) throughout (shift [= 0:NUM_STAGES-1]))
				##1 (test[i] == t)
				|-> ( (found[i] == 1'b1) && (dataout[i] == d) ));
		endproperty;

		check_tags_are_found: assert property(tags_are_found);
		cover_tags_are_found: cover property(tags_are_found);

		check_data_is_returned: assert property(data_is_returned);

		/** Only one match may be reported by index (the first one) */
		check_index_onehot: assert property(
			@(posedge clk) disable iff(reset)
			( $onehot0(index) )
		);
		// synopsys translate_on
		//---------------------------------------------------------------------------
	end : g_testport
endgenerate
//---------------------------------------------------------------------------


//---------------------------------------------------------------------------
// synopsys translate_off
initial begin
	// need only check parameter matching of interface and module once at
	// start of simulation
	check_tag_shiftreg_parameters: assert(
		TAG_SIZE == TAG_SIZE
		&& DATA_SIZE == DATA_SIZE
		&& NUM_STAGES == NUM_STAGES
		&& NUM_TESTPORTS == NUM_TESTPORTS
	);
end
// synopsys translate_on
//---------------------------------------------------------------------------

endmodule

