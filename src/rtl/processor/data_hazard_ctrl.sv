// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Data_hazard_ctrl
	(	input logic clk,
		input logic reset,

		Data_hazard_ctrl_if.data_hazard_ctrl  ctrl,
		Inst_fetch_ctrl_if.data_hazard_ctrl   if_ctrl,
		Decode_ctrl_if.data_hazard_ctrl       dc_ctrl,
		Bypass_if.control                     bypass);

	import Pu_types::*;


	logic[0:31] read_gpr;
	logic[0:31] write_gpr;
	logic[0:31] gpr_stalls;
	logic ctr_stall, lnk_stall;
	logic[0:7] cr_stall;
	logic xer_stall;
	
	logic en;
	assign en = ctrl.en;

	always_comb
	begin : comb_read_gpr
		logic[0:31] ra, rb, rc;

		ra = '0;
		rb = '0;
		rc = '0;

		ra[ctrl.gpr_a] = ctrl.read_gpr_a;
		rb[ctrl.gpr_b] = ctrl.read_gpr_b;
		rc[ctrl.gpr_c] = ctrl.read_gpr_c;

		read_gpr = ra | rb | rc;
	end : comb_read_gpr

	always_comb
	begin : comb_write_gpr
		logic[0:31] wa, wb;

		wa = '0;
		wb = '0;

		wa[ctrl.gpr_dest_alu] = ctrl.write_gpr_dest_alu;
		wb[ctrl.gpr_dest_mem] = ctrl.write_gpr_dest_mem;

		write_gpr = wa | wb;
	end : comb_write_gpr

	generate
		genvar i;
		for(i=0; i<32; ++i) begin : gpr_trackers
			Depend_track track(.*,
					.read(read_gpr[i]),
					.write(write_gpr[i]),
					.stall(gpr_stalls[i]));
		end : gpr_trackers
	endgenerate
			

	generate
		genvar j;
		for(j=0; j<8; ++j) begin : cr_trackers
			Depend_track track_cr(.*,
					.read(ctrl.read_cr[j]),
					.write(ctrl.write_cr[j]),
					.stall(cr_stall[j]));
		end
	endgenerate

	Depend_track track_ctr(.*,
			.read(ctrl.read_ctr),
			.write(ctrl.write_ctr),
			.stall(ctr_stall));

	Depend_track track_lnk(.*,
			.read(ctrl.read_lnk),
			.write(ctrl.write_lnk),
			.stall(lnk_stall));

	Depend_track track_xer(.*,
			.read(ctrl.read_xer),
			.write(ctrl.write_xer),
			.stall(xer_stall));

	assign if_ctrl.hold_data = (| {gpr_stalls, cr_stall, ctr_stall, lnk_stall, xer_stall});
	assign dc_ctrl.hold_data = (| {gpr_stalls, cr_stall, ctr_stall, lnk_stall, xer_stall});

endmodule


//---------------------------------------------------------------------------
// Track one dependend storage element accessed by instructions in the 
// pipeline.
//---------------------------------------------------------------------------
module Depend_track
	(	input logic clk, reset,
		input logic en,
		input logic read, write,
		output logic stall );

typedef enum { IDLE, EX, LS, WB } State;

State state;
State next_state;
logic stall_i;
logic lock_stall;
logic write_i, read_i;

assign write_i = write & en;
assign read_i = read & en;

always_ff @(posedge clk or posedge reset)
begin : state_transition
	if( reset ) begin
		state <= IDLE;
		lock_stall <= '0;
	end else begin
		state <= next_state;
		lock_stall <= stall_i;
	end
end : state_transition


always_comb
begin : calc_next_state
	unique case(state)
		IDLE:
			if( write_i )
				next_state = EX;
			else
				next_state = IDLE;

		EX: 
			if( write_i && !read_i )
				next_state = EX;
			else
				next_state = LS;

		LS: 
			if( write_i && !read_i )
				next_state = EX;
			else
				next_state = WB;

		WB: 
			if( write_i && !read_i )
				next_state = EX;
			else
				next_state = IDLE;
	endcase
end : calc_next_state


always_comb
begin : output_func
	if( state == IDLE )
		stall_i = 1'b0;
	else
		stall_i = read_i | lock_stall;
end : output_func

assign stall = stall_i;

endmodule
//---------------------------------------------------------------------------
