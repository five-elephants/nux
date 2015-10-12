// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Interrupt state machine
*
* Controlling state machine for control transfer when executing an interrupt.
* */
module Int_sm
	(	input logic       clk, reset,
		input logic       interrupt,
		input Address     vector,
		input Freeze_at   freeze_at,

		Inst_fetch_ctrl_if.int_sm  inst_fetch,
		Decode_ctrl_if.int_sm      decode,
		Branch_ctrl_if.int_sm      branch,
		Trap_ctrl_if.int_sm        trap,
		Load_store_ctrl_if.int_sm  load_store,
		Write_back_ctrl_if.int_sm  write_back );

import Pu_types::*;
import Pu_interrupt::*;

// internal types
typedef enum logic[7:0] { 
	S_IDLE         = 8'b0000_0001, 
	S_FREEZE_EX_0  = 8'b0000_0010,
	S_FREEZE_EX_1  = 8'b0000_0100,
	S_FREEZE_LS_0  = 8'b0000_1000,
	S_FREEZE_LS_1  = 8'b0001_0000,
	S_FREEZE_WB_0  = 8'b0010_0000,
	S_FREEZE_WB_1  = 8'b0100_0000,
	S_FREEZE_WB_2  = 8'b1000_0000,
	S_UNDEF        = 8'bxxxx_xxxx
} State;

// internal signals
State  state;

logic  store_ivect;

//---------------------------------------------------------------------------
// FSM state transitions
//---------------------------------------------------------------------------
always_ff @(posedge clk or posedge reset)
	if( reset )
		state <= S_IDLE;
	else begin
		unique case(state)
			S_IDLE: begin
				if( interrupt ) begin
					if( freeze_at == FREEZE_EX )
						state <= S_FREEZE_EX_0;
					else if( freeze_at == FREEZE_LS )
						state <= S_FREEZE_LS_0;
					else if( freeze_at == FREEZE_WB )
						state <= S_FREEZE_WB_0;
				end
			end

			S_FREEZE_EX_0:   state <= S_FREEZE_EX_1;
			S_FREEZE_EX_1:   state <= S_IDLE;
			S_FREEZE_LS_0:   state <= S_FREEZE_LS_1;
			S_FREEZE_LS_1:   state <= S_IDLE;
			S_FREEZE_WB_0:   state <= S_FREEZE_WB_1;
			S_FREEZE_WB_1:   state <= S_FREEZE_WB_2;
			S_FREEZE_WB_2:   state <= S_IDLE;
			default:         state <= S_UNDEF;
		endcase
	end

//---------------------------------------------------------------------------
// FSM output
//---------------------------------------------------------------------------

function void dont_jump();
	inst_fetch.int_jump = 1'b0;
	inst_fetch.hold_int = 1'b0;
	decode.hold_int = 1'b0;
endfunction

function void jump_0();
	inst_fetch.int_jump = 1'b1;
	inst_fetch.hold_int = 1'b1;
	decode.hold_int = 1'b1;
endfunction

function void jump_1();
	inst_fetch.int_jump = 1'b0;
	inst_fetch.hold_int = 1'b1;
	decode.hold_int = 1'b1;
endfunction

function void jump_undef();
	inst_fetch.int_jump = 1'bx;
	inst_fetch.hold_int = 1'bx;
	decode.hold_int = 1'bx;
endfunction


always_comb
begin
	// default assignment
	dont_jump();
	store_ivect = 1'b0;
	write_back.dis_ex = 1'b0;
	write_back.dis_ls = 1'b0;
	branch.en_int = 1'b1;
	load_store.en_int = 1'b1;
	write_back.en_int = 1'b1;
	trap.en_int = 1'b1;

	unique case(state)
		S_IDLE: begin
			store_ivect = 1'b1;
		end

		S_FREEZE_EX_0: begin
			jump_0();
			branch.en_int = 1'b0;
			trap.en_int = 1'b0;
			write_back.dis_ex = 1'b1;  // XXX pretty sure this is correct
		end

		S_FREEZE_EX_1: begin
			jump_1();
		end

		S_FREEZE_LS_0: begin
			jump_0();
			branch.en_int = 1'b0;
			trap.en_int = 1'b0;
			write_back.dis_ex = 1'b1;
			write_back.dis_ls = 1'b1;
			load_store.en_int = 1'b0;
		end

		S_FREEZE_LS_1: begin
			jump_1();
			write_back.dis_ls = 1'b1;
			load_store.en_int = 1'b0;
		end

		S_FREEZE_WB_0: begin
			jump_0();
			write_back.dis_ex = 1'b1;
			write_back.dis_ls = 1'b1;
			branch.en_int = 1'b0;
			trap.en_int = 1'b0;
			load_store.en_int = 1'b0;
			write_back.en_int = 1'b0;
		end

		S_FREEZE_WB_1: begin
			jump_1();
			write_back.dis_ls = 1'b1;
			load_store.en_int = 1'b0;
			write_back.en_int = 1'b0;
		end

		S_FREEZE_WB_2: begin
			dont_jump();
			write_back.en_int = 1'b0;
		end

		default: begin
			jump_undef();
			store_ivect = 1'bx;
			write_back.dis_ex = 1'bx;
			write_back.dis_ls = 1'bx;
			branch.en_int = 1'bx;
			load_store.en_int = 1'bx;
			write_back.en_int = 1'bx;
			trap.en_int = 1'bx;
		end
	endcase
end

//---------------------------------------------------------------------------
// Datapath
//---------------------------------------------------------------------------

/** Register the interrupt vector to IF */
always_ff @(posedge clk or posedge reset)
	if( reset )
		inst_fetch.int_vect <= '0;
	else begin
		if( store_ivect )
			inst_fetch.int_vect <= vector;
	end


endmodule
