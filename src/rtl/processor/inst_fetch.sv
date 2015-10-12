// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Inst_fetch 
	#(	parameter bit USE_OUTPUT_REG = 1'b1 )
	(	input logic clk,
		input logic reset,

		Inst_fetch_ctrl_if.inst_fetch     ctrl,
		Decode_data_if.inst_fetch         decode_data,
		Data_hazard_ctrl_if.inst_fetch    data_hazard,
		Int_sched_if.inst_fetch           int_sched,
		Register_file_if.inst_fetch       reg_file,
		Ram_if.client                     imem,
		
		Decode_ctrl_if.inst_fetch         decode,
		Branch_ctrl_if.int_sm             branch,
		Trap_ctrl_if.int_sm               trap,
		Fixedpoint_ctrl_if.int_sm         fixedpoint,
		Load_store_ctrl_if.int_sm         load_store,
		Write_back_ctrl_if.int_sm         write_back
	);

import Pu_types::*;
import Pu_inst::*;


//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

localparam Inst NOP = {6'd24, 26'b0};

typedef enum logic[12:0] {
	S_RESET            = 13'b0_0010_0000_0000,
	S_RESET_2          = 13'b1_0000_0000_0000,
	S_WAIT             = 13'b0_0100_0000_0000,
	S_HALTED           = 13'b0_0000_0000_0001,
	S_FETCHING         = 13'b0_0000_0000_0010,
	S_DELAYED          = 13'b0_0000_0000_0100,
	S_TRAN_FREEZE_DC   = 13'b0_1000_0000_0000,
	S_TRAN_FREEZE_EX   = 13'b0_0000_0000_1000,
	S_TRAN_FREEZE_LS_0 = 13'b0_0000_0001_0000,
	S_TRAN_FREEZE_LS_1 = 13'b0_0000_0010_0000,
	S_TRAN_FREEZE_WB_0 = 13'b0_0000_0100_0000,
	S_TRAN_FREEZE_WB_1 = 13'b0_0000_1000_0000,
	S_TRAN_FREEZE_WB_2 = 13'b0_0001_0000_0000,

	S_UNDEF            = 13'bx_xxxx_xxxx_xxxx
} State;

State       state;
Address     vector;
Freeze_at   freeze_at;
logic       jump;
Address     iaddr, next_iaddr;
Inst        inst;
logic       cancel_decode;
logic       is_branch;
logic[0:3]  speculative;
logic       spec_inval_i;
logic       tran_ip;
logic       wait_state;


//---------------------------------------------------------------------------
// Statemachine
//---------------------------------------------------------------------------

/** State transitions */
always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		state <= S_RESET;
		wait_state <= 1'b0;
	end else begin
		unique case(state)
			S_RESET: begin
				state <= S_RESET_2;
			end

			S_RESET_2: begin
				state <= S_FETCHING;
			end

			S_WAIT: begin
				if( jump ) begin
					unique case(freeze_at)
						FREEZE_DC:  state <= S_TRAN_FREEZE_DC;
						FREEZE_EX:  state <= S_TRAN_FREEZE_EX;
						FREEZE_LS:  state <= S_TRAN_FREEZE_LS_0;
						FREEZE_WB:  state <= S_TRAN_FREEZE_WB_0;
						default:    state <= S_UNDEF;
					endcase
				end

				wait_state <= 1'b0;
			end

			S_HALTED: begin
				if( jump ) begin
					unique case(freeze_at)
						FREEZE_DC:  state <= S_TRAN_FREEZE_DC;
						FREEZE_EX:  state <= S_TRAN_FREEZE_EX;
						FREEZE_LS:  state <= S_TRAN_FREEZE_LS_0;
						FREEZE_WB:  state <= S_TRAN_FREEZE_WB_0;
						default:    state <= S_UNDEF;
					endcase
				end else if( ctrl.if_wait )
					state <= S_WAIT;
				else if( !ctrl.hold )
					state <= S_FETCHING;
			end

			S_FETCHING: begin
				if( jump ) begin
					unique case(freeze_at)
						FREEZE_DC:  state <= S_TRAN_FREEZE_DC;
						FREEZE_EX:  state <= S_TRAN_FREEZE_EX;
						FREEZE_LS:  state <= S_TRAN_FREEZE_LS_0;
						FREEZE_WB:  state <= S_TRAN_FREEZE_WB_0;
						default:    state <= S_UNDEF;
					endcase
				end else if( ctrl.if_wait | wait_state )
					state <= S_WAIT;
				else if( ctrl.hold )
					state <= S_HALTED;
				else if( ctrl.if_wait )
					state <= S_WAIT;
				else if( imem.delay )
					state <= S_DELAYED;
			end

			S_DELAYED: begin
				if( jump ) begin
					unique case(freeze_at)
						FREEZE_DC:  state <= S_TRAN_FREEZE_DC;
						FREEZE_EX:  state <= S_TRAN_FREEZE_EX;
						FREEZE_LS:  state <= S_TRAN_FREEZE_LS_0;
						FREEZE_WB:  state <= S_TRAN_FREEZE_WB_0;
						default:    state <= S_UNDEF;
					endcase
				end else if( !imem.delay )
					state <= S_FETCHING;
			end

			S_TRAN_FREEZE_DC: begin
				if( imem.delay )
					state <= S_DELAYED;
				else
					state <= S_FETCHING;
			end

			S_TRAN_FREEZE_EX: begin
				if( imem.delay )
					state <= S_DELAYED;
				else
					state <= S_FETCHING;
			end

			S_TRAN_FREEZE_LS_0: begin
				state <= S_TRAN_FREEZE_LS_1;
			end

			S_TRAN_FREEZE_LS_1: begin
				if( imem.delay )
					state <= S_DELAYED;
				else if( ctrl.if_wait )
					state <= S_WAIT;
				else
					state <= S_FETCHING;

				wait_state <= ctrl.if_wait;
			end

			S_TRAN_FREEZE_WB_0: begin
				state <= S_TRAN_FREEZE_WB_1;
			end

			S_TRAN_FREEZE_WB_1: begin
				state <= S_TRAN_FREEZE_WB_2;
				wait_state <= ctrl.if_wait;
			end

			S_TRAN_FREEZE_WB_2: begin
				if( imem.delay )
					state <= S_DELAYED;
				else if( wait_state | ctrl.if_wait )
					state <= S_WAIT;
				else
					state <= S_FETCHING;

				wait_state <= ctrl.if_wait | wait_state;
			end

			default: begin
				state <= S_UNDEF;
			end
		endcase
	end


//---------------------------------------------------------------------------
/** Calculate the next instruction address */
function automatic Address calc_next_iaddr(input Address pc, new_pc, logic w, j, h);
	Address rv;

	if( reset )
		rv = pc;
	else if( j )
		rv = new_pc;
	else if( w || h )
		rv = pc;
	else
		rv = pc +1;

	return rv;
endfunction

function automatic Address calc_next_iaddr_nojump(input Address pc, logic w, h);
	Address rv;

	if( reset )
		rv = pc;
	else if( w || h )
		rv = pc;
	else
		rv = pc +1;

	return rv;
endfunction
//---------------------------------------------------------------------------

/** FSM output */
always_comb begin
	// default assignments
	decode.hold_if = 1'b0;
	next_iaddr = calc_next_iaddr(iaddr, vector, imem.delay, jump, ctrl.hold | ctrl.if_wait);
	imem.en = ~reset;
	// pipeline enable signals
	load_store.dis_ex = 1'b0;
	write_back.dis_ex = 1'b0;
	int_sched.dis_ex = 1'b0;
	int_sched.dis_ls = 1'b0;
	int_sched.dis_wb = 1'b0;
	write_back.dis_ls = 1'b0;
	write_back.dis_sleep = 1'b0;
	branch.en_int = 1'b1;
	load_store.en_int = 1'b1;
	write_back.en_int = 1'b1;
	trap.en_int = 1'b1;
	data_hazard.en = 1'b1;
	cancel_decode = 1'b0;
	tran_ip = 1'b0;
	fixedpoint.en_int = 1'b1;

	unique case(state)
		S_RESET: begin
			decode.hold_if = 1'b1;
			next_iaddr = '0;
			cancel_decode = 1'b1;
		end

		S_RESET_2: begin
			decode.hold_if = 1'b1;
		end

		S_WAIT: begin
			next_iaddr = calc_next_iaddr(iaddr, vector, 1'b1, jump, 1'b1);
			imem.en = jump;
			cancel_decode = 1'b1;
			write_back.dis_sleep = ctrl.int_jump;
		end

		S_HALTED: begin
			imem.en = ~ctrl.hold | jump;
			cancel_decode = jump | ctrl.if_wait;
			write_back.dis_sleep = ctrl.int_jump;
		end

		S_FETCHING: begin
			cancel_decode = jump | ctrl.if_wait;
		end

		S_DELAYED: begin
			cancel_decode = jump;
		end

		S_TRAN_FREEZE_DC: begin
			next_iaddr = calc_next_iaddr_nojump(iaddr, imem.delay, ctrl.hold | ctrl.if_wait | wait_state);
			decode.hold_if = 1'b1;
			data_hazard.en = 1'b0;
			branch.en_int = 1'b0;
			trap.en_int = 1'b0;
			write_back.dis_ex = 1'b1;
			load_store.dis_ex = 1'b1;
			int_sched.dis_ex = 1'b1;
			tran_ip = 1'b1;
			cancel_decode = ctrl.if_wait;
			write_back.dis_sleep = 1'b1;
		end

		S_TRAN_FREEZE_EX: begin
			next_iaddr = calc_next_iaddr_nojump(iaddr, imem.delay, ctrl.hold | ctrl.if_wait | wait_state);
			decode.hold_if = 1'b1;
			data_hazard.en = 1'b0;
			branch.en_int = 1'b0;
			trap.en_int = 1'b0;
			fixedpoint.en_int = 1'b0;
			write_back.dis_ex = 1'b1;  // XXX pretty sure this is correct
			load_store.dis_ex = 1'b1;
			int_sched.dis_ex = 1'b1;
			load_store.en_int = 1'b0;
			write_back.dis_ls = 1'b1;
			int_sched.dis_ls = 1'b1;
			write_back.dis_sleep = 1'b1;
			tran_ip = 1'b1;
			cancel_decode = ctrl.if_wait;
		end

		S_TRAN_FREEZE_LS_0: begin
			next_iaddr = calc_next_iaddr_nojump(iaddr, imem.delay, ctrl.hold | ctrl.if_wait | wait_state);
			decode.hold_if = 1'b1;
			data_hazard.en = 1'b0;
			branch.en_int = 1'b0;
			trap.en_int = 1'b0;
			fixedpoint.en_int = 1'b0;
			write_back.dis_ex = 1'b1;
			write_back.dis_ls = 1'b1;
			load_store.en_int = 1'b0;
			load_store.dis_ex = 1'b1;
			write_back.dis_sleep = 1'b1;
			int_sched.dis_ex = 1'b1;
			int_sched.dis_ls = 1'b1;
			tran_ip = 1'b1;
			cancel_decode = ctrl.if_wait;
		end

		S_TRAN_FREEZE_LS_1: begin
			next_iaddr = calc_next_iaddr_nojump(iaddr, imem.delay, ctrl.hold | ctrl.if_wait | wait_state);
			write_back.dis_ls = 1'b1;
			write_back.dis_sleep = 1'b1;
			load_store.en_int = 1'b0;
			int_sched.dis_ls = 1'b1;
			tran_ip = 1'b1;
			cancel_decode = wait_state | ctrl.if_wait;
		end

		S_TRAN_FREEZE_WB_0: begin
			next_iaddr = calc_next_iaddr_nojump(iaddr, imem.delay, ctrl.hold | ctrl.if_wait | wait_state);
			decode.hold_if = 1'b1;
			data_hazard.en = 1'b0;
			load_store.dis_ex = 1'b1;
			write_back.dis_ex = 1'b1;
			write_back.dis_ls = 1'b1;
			write_back.dis_sleep = 1'b1;
			branch.en_int = 1'b0;
			trap.en_int = 1'b0;
			fixedpoint.en_int = 1'b0;
			load_store.en_int = 1'b0;
			write_back.en_int = 1'b0;
			int_sched.dis_ex = 1'b1;
			int_sched.dis_ls = 1'b1;
			int_sched.dis_wb = 1'b1;
			tran_ip = 1'b1;
			cancel_decode = ctrl.if_wait;
		end

		S_TRAN_FREEZE_WB_1: begin
			next_iaddr = calc_next_iaddr_nojump(iaddr, imem.delay, ctrl.hold | ctrl.if_wait | wait_state);
			write_back.dis_ls = 1'b1;
			load_store.en_int = 1'b0;
			write_back.en_int = 1'b0;
			write_back.dis_sleep = 1'b1;
			int_sched.dis_ls = 1'b1;
			int_sched.dis_wb = 1'b1;
			tran_ip = 1'b1;
			cancel_decode = wait_state | ctrl.if_wait;
		end

		S_TRAN_FREEZE_WB_2: begin
			next_iaddr = calc_next_iaddr_nojump(iaddr, imem.delay, ctrl.hold | ctrl.if_wait | wait_state);
			write_back.en_int = 1'b0;
			write_back.dis_sleep = 1'b1;
			int_sched.dis_wb = 1'b1;
			tran_ip = 1'b1;
			cancel_decode = wait_state | ctrl.if_wait;
		end
			
		default: begin
			decode.hold_if = 1'bx;
			cancel_decode = 1'bx;
			data_hazard.en = 1'bx;
			next_iaddr = 'x;
			load_store.dis_ex = 1'bx;
			write_back.dis_ex = 1'bx;
			int_sched.dis_ex = 1'bx;
			write_back.dis_ls = 1'bx;
			write_back.dis_sleep = 1'bx;
			int_sched.dis_ls = 1'bx;
			branch.en_int = 1'bx;
			load_store.en_int = 1'bx;
			write_back.en_int = 1'bx;
			trap.en_int = 1'bx;
			int_sched.dis_wb = 1'bx;
			tran_ip = 1'bx;
			fixedpoint.en_int = 1'bx;
		end
	endcase
end

//---------------------------------------------------------------------------
// Datapath
//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
	if( reset )
		iaddr <= '0;
	else
		iaddr <= next_iaddr;

/** Output register stage */
always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		decode_data.npc <= '0;
		decode_data.pc  <= '0;
		inst            <= NOP;
		int_sched.pc    <= '0;
	end else begin
		if( !ctrl.hold ) begin
			decode_data.npc <= next_iaddr;
			decode_data.pc  <= iaddr;
			int_sched.pc    <= iaddr;
		end

		if( cancel_decode ) begin
			inst <= NOP;
		end else if( !ctrl.hold ) begin
			if( !imem.delay )
				inst <= imem.data_r;
			else
				inst <= NOP;
		end
	end


/** Demultiplex control transfer request inputs */
always_comb begin
	if( ctrl.int_jump ) begin
		vector = ctrl.int_vect;
		freeze_at = ctrl.freeze_at;
	end else begin
		vector = ctrl.new_pc;
		freeze_at = FREEZE_LS;
	end

	jump = ctrl.int_jump | ctrl.jump;
end


/** Directly assign register file read port addresses from fetched instruction
* word */
always_comb begin
	Inst tmp;
	tmp = imem.data_r;

	if( !imem.delay && !ctrl.hold ) begin
		reg_file.gpr_sel_a = tmp.xo.ra;
		reg_file.gpr_sel_b = tmp.xo.rb;
		reg_file.gpr_sel_c = tmp.xo.rt;
	end else begin
		reg_file.gpr_sel_a = inst.xo.ra;
		reg_file.gpr_sel_b = inst.xo.rb;
		reg_file.gpr_sel_c = inst.xo.rt;
	end

	if( ctrl.gpr_sel_c_over )
		reg_file.gpr_sel_c = ctrl.gpr_sel_c;
end

//---------------------------------------------------------------------------
// Static assignments
//---------------------------------------------------------------------------

assign imem.addr = next_iaddr[$left(imem.addr):$right(imem.addr)];

// unused write port
assign imem.data_w = '0;
assign imem.we = 1'b0;
assign imem.be = '0;

assign decode_data.inst = inst;
assign int_sched.tran_ip = tran_ip;

//---------------------------------------------------------------------------
// Detection of branches
//---------------------------------------------------------------------------

always_comb begin
	logic[14:0] cop;
	Inst tmp_inst;

	tmp_inst = imem.data_r;

	cop = {tmp_inst.xl.opcd, tmp_inst.xl.xo};
	unique casez(cop)
		{Op_bc, 10'bz}, {Op_branch, 10'bz},
		{Op_bclr, Xxop_bclr}, {Op_bclr, Xxop_bcctr}, {Op_bclr, Xxop_rfi},
		{Op_bclr, Xxop_rfci}, {Op_bclr, Xxop_rfmci}:
			is_branch = 1'b1;

		default: 
			is_branch = 1'b0;
	endcase
end


always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		for(int i=0; i<$bits(speculative); i++)
			speculative[i] <= 1'b0;
		
		spec_inval_i <= 1'b0;
	end else begin
		if( spec_inval_i ) begin
			if( !ctrl.hold ) begin
				speculative[0] <= is_branch;
			end
			
			for(int i=1; i<$bits(speculative); i++)
				speculative[i] <= 1'b0;
		end else begin
			if( !ctrl.hold ) begin
				speculative[0] <= is_branch;
			end
			
			speculative[1] <= speculative[0] & ~ctrl.hold;
			
			for(int i=2; i<$bits(speculative); i++)
				speculative[i] <= speculative[i-1];
		end
		
		spec_inval_i <= jump;
	end

/*always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    for(int i=0; i<$bits(speculative); i++)
      speculative[i] <= 1'b0;

    spec_inval_i <= 1'b0;
  end else begin
    if( !ctrl.hold ) begin
      speculative[0] <= is_branch;
    end

    speculative[1] <= speculative[0] & ~ctrl.hold;

    for(int i=2; i<$bits(speculative); i++)
      speculative[i] <= speculative[i-1];

    spec_inval_i <= jump;
  end*/


assign int_sched.speculative =  (| speculative[1:$right(speculative)]);
assign int_sched.spec_inval = spec_inval_i;
//---------------------------------------------------------------------------


endmodule


// vim: noexpandtab ts=4 sw=4 softtabstop=0 nosmarttab:
