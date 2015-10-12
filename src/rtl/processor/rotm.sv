// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Rotate (left) and mask
 * 
 * Rotate word x by num bits to the left and and with mask generated from
 * mstart and mend. mstart and mend use the bitnumbering from the PowerISA
 * spec: 0 is the most significant bit, 31 the least significant one.
 * */
module Rotm
	(	input logic clk, reset,
		input Pu_types::Word x,
		input Pu_types::Word q,
		input logic[4:0] num,
		input logic[4:0] mstart,
		input logic[4:0] mstop,
		output Pu_types::Word y,
		output logic cout,
		output Pu_types::Cr_field cr);

import Pu_types::*;

Word rotated;
logic[0:DWIDTH-1] mask;
logic[0:DWIDTH-1] a, b;     // start and stop signals for mask generation
Word[5:0] stages;           // barrel shifter intermediate stages
Word[5:1] stages_sh;
Word y_i;
Cr_field cr_i;
logic cout_i;
//---------------------------------------------------------------------------
/** Barrel-shifter build from multiplexers */
generate 
/*
	genvar i;
	for(i=0; i<DWIDTH; ++i) begin : rot_muxes
		always_comb
		begin
			logic[4:0] sel;
			sel = i - num;
			rotated[i] = x[sel];
		end
	end : rot_muxes 
*/
	//
	// This alternative version consumes much less area
	// (actually the effect is not that drastic when targetting FPGAs)
	//
	assign rotated = stages[0];
	always_comb stages[5] = x;

	genvar i;
	for(i=5; i>0; i--) begin : shift
		always_comb
			for(int b=0; b<DWIDTH; b++)
				stages_sh[i][(b + 2**(i-1)) % DWIDTH] = stages[i][b];
	end : shift

	for(i=4; i>=0; i--) begin : mux
		always_comb 
			if( num[i] == 1'b0 )
				stages[i] = stages[i+1];
			else
				stages[i] = stages_sh[i+1];
	end : mux
endgenerate
//---------------------------------------------------------------------------
/** Generate mask from one-hot coded start and stop bits */
generate
	genvar j;
	for(j=0; j<DWIDTH; j++) begin : gen_mask
		assign mask[j] = ((| a[0:j]) & (| a[j:DWIDTH-1])) | ((| b[0:j]) & (| b[j:DWIDTH-1]));
	end
endgenerate
//---------------------------------------------------------------------------
/** Generate "one-hot" start and stop signals a and b */
always_comb
begin : one_hot
	a = '0;
	b = '0;

	if( mstart <= mstop ) begin
		a[mstart] = 1'b1;
		a[mstop] = 1'b1;
	end else begin
		a[mstart] = 1'b1;
		a[DWIDTH-1] = 1'b1;
		b[0] = 1'b1;
		b[mstop] = 1'b1;
	end
end : one_hot
//---------------------------------------------------------------------------
assign y_i = (rotated & mask) | (q & ~mask);
assign cout_i = x[DWIDTH-1] & (| (rotated & ~mask));
//---------------------------------------------------------------------------

/** Calculate output condition bits */
always_comb
begin
	// default assignments
	cr_i = '0;

	if( y_i[$left(y_i)] == 1'b1 )  // negative
		cr_i.lt = 1'b1;
	else if( (| y_i) == 1'b0 )  // zero
		cr_i.eq = 1'b1;
	else  // positive
		cr_i.gt = 1'b1;
end

//---------------------------------------------------------------------------
// Output register
//---------------------------------------------------------------------------
//always_ff @(posedge clk or posedge reset)
	//if( reset ) begin
		//y <= '0;
		//cr <= '0;
		//cout <= 1'b0;
	//end else begin
		//y <= y_i;
		//cr <= cr_i;
		//cout <= cout_i;
	//end
always_comb begin
		y = y_i;
		cr = cr_i;
		cout = cout_i;
	end

endmodule
