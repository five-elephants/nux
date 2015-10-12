// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Select byte, halfword or word from input and present it aligned on the ouput
 * */
module Byte_align
	(	input Pu_types::Word        d,
		input Pu_types::Load_mode   mode,
		input logic[1:0]            bsel,
		output Pu_types::Word       y );

import Pu_types::*;

logic[2:0] s;
logic[7:0] mux2o;
logic[7:0] mux1o;
logic[7:0] mux0o;

//---------------------------------------------------------------------------
// Calculate multiplexer output and gate enables
//---------------------------------------------------------------------------
always_comb
	if( mode == Load_byte || (mode == Load_halfword && bsel[1]) )
		s[0] = 1'b0;
	else
		s[0] = 1'b1;

always_comb
	if( mode == Load_byte || (mode == Load_halfword && bsel == 2'b00) )
		s[1] = 1'b0;
	else
		s[1] = 1'b1;

always_comb
	if( mode == Load_byte || (mode == Load_halfword && bsel[1] == 1'b0) )
		s[2] = 1'b0;
	else
		s[2] = 1'b1;

//---------------------------------------------------------------------------
// Combine multiplexer output to output word
//---------------------------------------------------------------------------
always_comb
begin
	y = '0;

	if( mode == Load_word )
		y = { d[31:24], mux2o, mux1o, mux0o };
	else if( mode == Load_halfword )
		y = { 16'h0, mux0o, mux1o };
	else
		y = { 24'h0, mux0o };

/*
	if( mode == Load_word )
		y[31:24] = d[31:24];
	
	if( mode == Load_word )
		y[23:16] = mux2o;

	if( mode == Load_halfword || mode == Load_word )
		y[15:8] = mux1o;

	y[7:0] = mux0o;
*/
end

//---------------------------------------------------------------------------
// Multiplexers
//---------------------------------------------------------------------------
always_comb
begin : mux2
	unique case(bsel[0])
		1'b1:  mux2o = d[23:16];
		1'b0:  mux2o = d[31:24];
	endcase
end : mux2

always_comb
begin : mux1
	unique case(bsel)
		2'b10:   mux1o = d[7:0];
		2'b01:   mux1o = d[15:8];
		2'b00:   mux1o = d[23:16];
		default: mux1o = d[31:24];
	endcase
end : mux1

always_comb
begin : mux0
	unique case(bsel)
		2'b11:   mux0o = d[7:0];
		2'b10:   mux0o = d[15:8];
		2'b01:   mux0o = d[23:16];
		2'b00:   mux0o = d[31:24];
	endcase
end : mux0


endmodule
