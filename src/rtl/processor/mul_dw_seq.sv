// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Multiplier using the DesignWare sequential multiplier */
module Mul_dw_seq
	(	input logic     clk, reset,
		input logic     en,
		input logic     uns,
		input Word      a, b,
		output logic    ready,
		output logic    complete,
		output Word     res_hi, res_lo,
		output Cr_field crf_hi, crf_lo);

import Pu_types::*;

localparam int STAGES = 8;

// internal types
typedef enum logic[3:0] { 
	S_INIT      = 4'b0001,
	S_IDLE      = 4'b0010,
	S_ON        = 4'b0100,
	S_COMPLETE  = 4'b1000,
	S_UNDEF     = 4'bxxxx
} State;

// internal signals
logic[2*DWIDTH-1:0]  s_prod;
logic                s_start;
logic                s_complete;
logic[2*DWIDTH-1:0]  u_prod;
logic                u_start;
logic                u_complete;

State                state;

//---------------------------------------------------------------------------
// Controlling state machine
//---------------------------------------------------------------------------
always_ff @(posedge clk or posedge reset)
	if( reset )
		state <= S_INIT;
	else
		unique case(state)
			S_INIT: begin
				if( s_complete | u_complete )
					state <= S_IDLE;
				else
					state <= S_INIT;
			end

			S_IDLE: begin
				if( en )
					state <= S_ON;
				else
					state <= S_IDLE;
			end

			S_ON: begin
				if( s_complete | u_complete )
					state <= S_COMPLETE;
				else
					state <= S_ON;
			end

			S_COMPLETE: begin
				state <= S_IDLE;
			end

			default: begin
				state <= S_UNDEF;
			end
		endcase

always_comb
begin
	// default assignment
	s_start = 1'b0;
	u_start = 1'b0;
	ready = 1'b0;
	complete = 1'b0;

	unique case(state)
		S_INIT: begin
		end

		S_IDLE: begin
			s_start = en;  // & ~uns;
			u_start = en;  // &  uns;
			ready = 1'b1;
		end

		S_ON: begin
			complete = s_complete | u_complete;
		end

		S_COMPLETE: begin
			complete = 1'b0;
			ready = 1'b0;
		end

		default: begin
			s_start = 1'bx;
			u_start = 1'bx;
			ready = 1'bx;
			complete = 1'bx;
		end
			
	endcase
end

// Instance of DW_mult_seq
DW_mult_seq
	#(	.a_width(DWIDTH),
		.b_width(DWIDTH),
		.tc_mode(1),        // two's complement multiplier
		.num_cyc(STAGES),
		.rst_mode(0),       // async reset
		.input_mode(1),     // input registers
		.output_mode(1),    // output registers
		.early_start(0) )
	mult_seq_sgnd
	(	.clk(clk),
		.rst_n(~reset),
		.hold(1'b0),
		.start(s_start),
		.a(a),
		.b(b),
		.complete(s_complete),
		.product(s_prod) );

DW_mult_seq
	#(	.a_width(DWIDTH),
		.b_width(DWIDTH),
		.tc_mode(0),        // unsigned multiplier
		.num_cyc(STAGES),
		.rst_mode(0),       // async reset
		.input_mode(1),     // no input registers
		.output_mode(1),    // no output registers
		.early_start(0) )
	mult_seq_unsgnd
	(	.clk(clk),
		.rst_n(~reset),
		.hold(1'b0),
		.start(u_start),
		.a(a),
		.b(b),
		.complete(u_complete),
		.product(u_prod) );


always_ff @(posedge clk or posedge reset)
	if( reset )
		{res_hi, res_lo} <= '0;
	else
		if( s_complete | u_complete )
			if( uns )
				{res_hi, res_lo} <= u_prod;
			else
				{res_hi, res_lo} <= s_prod;

//---------------------------------------------------------------------------
// Generate compare bits
//---------------------------------------------------------------------------
Cr_field next_crf_lo;
Cr_field next_crf_hi;

always_comb begin
	Word res_hi_i;
	Word res_lo_i;

	// default assignment
	next_crf_lo = '0;
	next_crf_hi = '0;

	if( uns ) begin
		res_hi_i = u_prod[63:32];
		res_lo_i = u_prod[31: 0];
	end else begin
		res_hi_i = s_prod[63:32];
		res_lo_i = s_prod[31: 0];
	end

	unique if( res_hi_i[$left(res_hi_i)] == 1'b1 ) begin  // negative
		next_crf_hi.lt = 1'b1;
	end else if( (| res_hi_i[DWIDTH-1:0]) == 1'b0 )  // zero
		next_crf_hi.eq = 1'b1;
	else begin // positive
		next_crf_hi.gt = 1'b1;
	end

	unique if( res_lo_i[$left(res_lo_i)] == 1'b1 ) begin  // negative
		next_crf_lo.lt = 1'b1;
	end else if( (| res_lo_i[DWIDTH-1:0]) == 1'b0 )  // zero
		next_crf_lo.eq = 1'b1;
	else begin // positive
		next_crf_lo.gt = 1'b1;
	end

	// overflow if result can not be represented in the low word
	// -> check equivalency of low word sign bit and all high word bits
	next_crf_lo.ov = (| ({DWIDTH {res_lo_i[$left(res_lo_i)]}} ^ res_hi_i));
end

always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		crf_hi <= '0;
		crf_lo <= '0;
	end else begin
		crf_hi <= next_crf_hi;
		crf_lo <= next_crf_lo;
	end
//---------------------------------------------------------------------------


endmodule
