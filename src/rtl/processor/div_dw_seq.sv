// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Div_dw_seq
	(	input logic                clk, reset,
		input logic                en,
		input logic                uns,

		input Pu_types::Word       a, b,

		output logic               ready,
		output logic               complete,
		output Pu_types::Word      quotient,
		output Pu_types::Word      remainder,
		output logic               div_by_zero,
		output Pu_types::Cr_field  crf );

import Pu_types::*;

//localparam int STAGES = 24;//32;
localparam int STAGES = Frontend::div_latency - 4;

// internal types
typedef enum logic[3:0] { 
	S_INIT      = 4'b0001, 
	S_IDLE      = 4'b0010, 
	S_ON        = 4'b0100, 
	S_COMPLETE  = 4'b1000,
	S_UNDEF     = 4'bxxxx
} State;

// local signals
logic[DWIDTH:0] a_ext, b_ext;
logic  s_start, u_start;
logic  s_complete, u_complete;
logic  s_div_by_zero, u_div_by_zero;
Word   s_quotient, u_quotient;
logic  u_quot_ext;
Word   s_remainder, u_remainder;
logic  u_rem_ext;
Word   next_quotient, next_remainder;
logic  a_sgn, b_sgn;
logic  illegal_signed_ops;
logic  uns_d;
logic complete_i;

State  state;

//---------------------------------------------------------------------------
// Controlling state machine
//---------------------------------------------------------------------------
always_ff @(posedge clk or posedge reset)
	if( reset )
		state <= S_INIT;
	else
		unique case(state)
			S_INIT: begin
				if( u_complete )
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
				/*if( !en )
					state <= S_IDLE;
				else*/ if( u_complete )
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
	complete_i = 1'b0;

	unique case(state)
		S_INIT: begin
		end

		S_IDLE: begin
			s_start = en;  // & ~uns;
			u_start = en;  // &  uns;
			ready = 1'b1;
		end

		S_ON: begin
			complete_i = u_complete;
		end

		S_COMPLETE: begin
			complete_i = 1'b0;
			ready = 1'b0;
		end

		default: begin
			s_start = 1'bx;
			u_start = 1'bx;
			ready = 1'bx;
			complete_i = 1'bx;
		end
	endcase
end

always_ff @(posedge clk)
	complete <= complete_i;


// Instances of DW_div_seq
//DW_div_seq
	//#(	.a_width(DWIDTH),
		//.b_width(DWIDTH),
		//.tc_mode(1),         // signed division
		//.num_cyc(STAGES),
		//.rst_mode(0),        // async reset
		//.input_mode(1),      // input registers
		//.output_mode(1),     // output registers
		//.early_start(0) )
	//div_seq_sgnd
	//(	.clk(clk),
		//.rst_n(~reset),
		//.hold(1'b0),
		//.start(s_start),
		//.a(a),
		//.b(b),
		//.complete(s_complete),
		//.divide_by_0(s_div_by_zero),
		//.quotient(s_quotient),
		//.remainder(s_remainder) );

assign a_ext = {~uns & a[DWIDTH-1], a};
assign b_ext = {~uns & b[DWIDTH-1], b};

DW_div_seq
	#(	.a_width(DWIDTH+1),
		.b_width(DWIDTH+1),
		.tc_mode(1),         // signed division
		.num_cyc(STAGES),
		.rst_mode(0),        // async reset
		.input_mode(1),      // no input registers
		.output_mode(1),     // no output registers
		.early_start(0) )
	div_seq_unsgnd
	(	.clk(clk),
		.rst_n(~reset),
		.hold(1'b0),
		.start(u_start),
		.a(a_ext),
		.b(b_ext),
		.complete(u_complete),
		.divide_by_0(u_div_by_zero),
		.quotient({u_quot_ext, u_quotient}),
		.remainder({u_rem_ext, u_remainder}) );

always_ff @(posedge clk)
begin
	if( state == S_IDLE ) begin
		a_sgn <= a[$left(a)];
		b_sgn <= b[$left(b)];

		illegal_signed_ops <= (a == 32'h80000000 && b == 32'hffffffff);

		uns_d <= uns;
	end
end


always_comb begin
	if( uns_d ) begin
		next_quotient = u_quotient;
		next_remainder = u_remainder;
	end else begin
		// negate the result if exactly one input is negative
		//if( a_sgn ^ b_sgn ) begin
			//next_quotient = ~u_quotient + 1;
			//next_remainder = 'x;
		//end else begin
			next_quotient = u_quotient;
			next_remainder = u_remainder;
		//end
	end
end

always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		quotient <= '0;
		remainder <= '0;
	end else begin
		quotient <= next_quotient;
		remainder <= next_remainder;
	end


//---------------------------------------------------------------------------
// Generate compare bits
//---------------------------------------------------------------------------
Cr_field next_crf;
logic    next_div_by_zero;

always_comb begin
	Word res;

	// default assignment
	next_crf = '0;

	res = next_quotient;	

	unique if( res[$left(res)] == 1'b1 ) begin  // negative
		next_crf.lt = 1'b1;
	end else if( (| res[DWIDTH-1:0]) == 1'b0 )  // zero
		next_crf.eq = 1'b1;
	else begin // positive
		next_crf.gt = 1'b1;
	end

	// Overflow if an illegal division was performed.
	// Divide by zero or for signed division: Largest negative number by -1
	if( uns_d )
		next_crf.ov = u_div_by_zero;
	else
		next_crf.ov = u_div_by_zero || illegal_signed_ops;

	// divide by zero output
	next_div_by_zero = u_div_by_zero | s_div_by_zero;
end


always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		crf <= '0;
	end else begin
		crf <= next_crf;
		div_by_zero <= next_div_by_zero;
	end
//---------------------------------------------------------------------------

endmodule
