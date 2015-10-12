// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Mul
	(	input logic     clk, reset,
		
		input logic     uns,
		input Word      a, b,
		output Word     res_hi, res_lo,
		output Cr_field crf_hi, crf_lo);

import Pu_types::*;

Word res_hi_i, res_lo_i;
Word[0:1] rsh[0:31];
//---------------------------------------------------------------------------
always_comb
	if( uns )
		{res_hi_i, res_lo_i} = unsigned'({32'b0, a}) * unsigned'({32'b0, b});
	else
		{res_hi_i, res_lo_i} = signed'(a) * signed'(b);


always_ff @(posedge clk)
begin
	for(int i=1; i<32; i++) begin
		rsh[i-1] <= rsh[i];
	end

	rsh[31] <= {res_hi_i, res_lo_i};
end

//assign {res_hi, res_lo} = rsh[0];

always_ff @(posedge clk or posedge reset)
	if( reset )
		{res_hi, res_lo} <= '0;
	else
		{res_hi, res_lo} <= {res_hi_i, res_lo_i};


always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		crf_hi <= '0;
		crf_lo <= '0;
	end else begin
		// default assignment
		crf_lo <= '0;
		crf_hi <= '0;

		unique if( res_hi_i[$left(res_hi_i)] == 1'b1 ) begin  // negative
			crf_hi.lt <= 1'b1;
		end else if( (| res_hi_i[DWIDTH-1:0]) == 1'b0 )  // zero
			crf_hi.eq <= 1'b1;
		else begin // positive
			crf_hi.gt <= 1'b1;
		end

		unique if( res_lo_i[$left(res_lo_i)] == 1'b1 ) begin  // negative
			crf_lo.lt <= 1'b1;
		end else if( (| res_lo_i[DWIDTH-1:0]) == 1'b0 )  // zero
			crf_lo.eq <= 1'b1;
		else begin // positive
			crf_lo.gt <= 1'b1;
		end

		// overflow if result can not be represented in the low word
		// -> check equivalency of low word sign bit and all high word bits
		crf_lo.ov <=(| ({DWIDTH {res_lo_i[$left(res_lo_i)]}} ^ res_hi_i));
	end
//---------------------------------------------------------------------------

endmodule
