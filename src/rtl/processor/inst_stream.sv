// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Instruction streaming unit
*
* This module streams instructions from a memory with prediction of branches.
* The downstream logic has to indicate the outcome of branches and theire
* destination.
* A control transfer is started by asserting the jump signal together with the
* target location given via jump_vec. The completetion of the transfer is
* indicated by trans_cmplt. In the same cycle instruction and PC from the
* target location are presented on inst and pc.
* predicted_taken is asserted together with the instruction that was assumed
* to be a taken branch. If the prediction is false it has to be corrected by
* initiating a control transfer to the correct location. Downstream logic has
* to check the prediction and the predicted target.
* */
module Inst_stream
	#(	/** Width of instruction memory addresses. */
		parameter int addr_width = 32, //14
		/** Turn the branch prediction on or off. */
		parameter bit use_bcache = 1'b1,
		/** Width of branch prediction cache addresses. */
		parameter int bcache_width = 8,
		/** Number of output register stages after the instruction memory. */
		parameter int output_delay = 3,
		parameter bit bcache_ignores_jumps = 1'b0,
   		parameter bit buffer_bctrl = 1'b1 )
	(	input logic clk, reset,

		/** Interface port to the instruction memory. */
		Ram_if.client                   imem,

		/** Stop the instruction fetching pipeline. */
		input logic                     hold,

		input Frontend::Branch_control  bctrl,
		output Frontend::Fetch_state    fst );

import Frontend::*;


//---------------------------------------------------------------------------
// Local types & signals
//---------------------------------------------------------------------------

typedef logic[addr_width-1:0] Addr;

Frontend::Branch_control bctrl_d;

Addr iaddr, next_iaddr;
Addr local_next_iaddr;
Addr iaddr_inc;
Addr iaddr_d;
Pu_inst::Inst data_r;

logic p_taken;
Addr  p_target;

logic en_shift;

logic delay_d;

//---------------------------------------------------------------------------
// Logic
//---------------------------------------------------------------------------


generate if( buffer_bctrl ) begin : gen_buf_bctrl

	always_ff @(posedge clk or posedge reset)
		if( reset ) begin
			//{>>{bctrl_d}} <= {$bits(bctrl_d){1'b0}};
			bctrl_d.jump <= 1'b0;
			bctrl_d.jump_vec <= '0;
			bctrl_d.fb_taken <= 1'b0;
			bctrl_d.fb_not_taken <= 1'b0;
			bctrl_d.fb_pc <= '0;
		end else
			bctrl_d <= bctrl;

end : gen_buf_bctrl
else
begin : gen_no_buf_bctrl

	assign bctrl_d = bctrl;

end : gen_no_buf_bctrl
endgenerate


assign imem.en = ~hold;
assign imem.addr = iaddr;
assign imem.data_w = '0;
assign imem.we = 1'b0;
assign imem.be = '0;

always_comb begin
	local_next_iaddr = iaddr_inc;

	if( imem.delay )
		local_next_iaddr = iaddr_d;
	else if( hold )
		local_next_iaddr = iaddr;
	else
		if( p_taken )
			local_next_iaddr = p_target;
		else
			local_next_iaddr = iaddr_inc;
end

always_comb begin
	if( bctrl_d.jump ) 
		next_iaddr = bctrl_d.jump_vec;
	else
		next_iaddr = local_next_iaddr;
end

always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		iaddr <= '0;
		iaddr_d <= '0;
	end else begin
		iaddr <= next_iaddr;

		if( bctrl_d.jump )
			iaddr_d <= bctrl_d.jump_vec;
		else if( !imem.delay )
			iaddr_d <= iaddr;
	end


always_ff @(posedge clk or posedge reset)
	if( reset )
		delay_d <= 1'b0;
	else begin
		if( !hold )
			delay_d <= imem.delay;
	end

assign iaddr_inc = iaddr + 1;
assign data_r = ((delay_d || imem.delay) ? Pu_inst::INST_NOP : imem.data_r);

//---------------------------------------------------------------------------
// Submodules
//---------------------------------------------------------------------------

generate if( use_bcache ) begin : gen_use_bcache
	Addr bcache_addr;
	logic ignore_predict;
	logic p_taken_pre;

	if( bcache_ignores_jumps == 1'b1 ) begin : gen_ignore_jumps
		assign bcache_addr = local_next_iaddr;

		always_ff @(posedge clk or posedge reset)
			if( reset )
				ignore_predict = 1'b0;
			else
				ignore_predict = bctrl_d.jump;
	end else begin : gen_no_ignore_jumps
		assign bcache_addr = next_iaddr;
		assign ignore_predict = 1'b0;
	end

	//Bcache #( 
		//.lookup_width(bcache_width),
		//.addr_width(addr_width)
	//) bcache (
	Bcache_full #(
		.table_size(2**bcache_width),
		.addr_width(addr_width)
	) bcache_full (
		.clk, .reset,
		//.addr(next_iaddr),
		.addr(bcache_addr),
		.jump(bctrl_d.jump),
		.jump_vec(bctrl_d.jump_vec),
		.taken(bctrl_d.fb_taken),
		.not_taken(bctrl_d.fb_not_taken),
		.pc(bctrl_d.fb_pc),
		.predict_taken(p_taken_pre),
		.predict_target(p_target)
	);

	assign p_taken = p_taken_pre & ~ignore_predict;
end : gen_use_bcache
else
begin : gen_no_bcache
	assign
		p_taken = 1'b0,
		p_target = '0;
end : gen_no_bcache
endgenerate


assign en_shift = ~hold | bctrl_d.jump;
//assign en_shift = ~hold;

/** Output delay stage */
Shift_reg #( .depth(2+output_delay), .width(1) ) sh_trans_cmplt (
	.*,
	.en(en_shift),
	.in(bctrl_d.jump),
	.out(fst.trans_cmplt)
);

Shift_reg #( .depth(1+output_delay), .width($bits(fst.npc)) ) sh_npc (
	.*,
	.en(en_shift),
	.in(next_iaddr),
	.out(fst.npc)
);

Shift_reg #( .depth(1+output_delay), .width($bits(fst.pc)) ) sh_pc (
	.*,
	.en(en_shift),
	.in(iaddr),
	.out(fst.pc)
);

Shift_reg #( .depth(output_delay), .width($bits(fst.inst)) ) sh_inst (
	.*,
	.en(en_shift),
	.in(data_r),
	.out(fst.inst)
);

Shift_reg #( .depth(1+output_delay), .width(1) ) sh_p_taken (
	.*,
	.en(en_shift),
	.in(p_taken),
	.out(fst.predicted_taken)
);

Shift_reg #( .depth(1+output_delay), .width(1) ) sh_valid (
	.*,
	.en(en_shift),
	.in(1'b1),
	.out(fst.valid)
);

endmodule


//---------------------------------------------------------------------------
module Shift_reg
	#( parameter int depth = 3,
		parameter int width = 1 )
	( input logic clk, reset,
		input logic en,
		input logic[width-1:0] in,
		output logic[width-1:0] out );

	generate if( depth > 0 ) begin : gen_pos_depth
		logic[width-1:0] stages[0:depth-1];

		always_ff @(posedge clk or posedge reset)
			if( reset ) begin
				for(int i=0; i<depth; i++)
					stages[i] <= '0;
			end else begin
				if( en ) begin
					stages[0] <= in;

					for(int i=1; i<depth; i++)
						stages[i] <= stages[i-1];
				end
			end

		assign out = stages[depth-1];
	end : gen_pos_depth
	else
	begin : gen_zero_depth
		assign out = in;
	end : gen_zero_depth
	endgenerate

endmodule
//---------------------------------------------------------------------------


// vim: noexpandtab ts=4 sw=4 softtabstop=0 nosmarttab:
