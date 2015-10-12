// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Dec_mem_multiple
	(	input logic clk, reset,

		Decode_ctrl_if.decode ctrl,
		Decode_data_if.decode data,

		output Control_word cw
	);

import Pu_types::*;
import Pu_inst::*;


typedef enum logic[4:0] { 
	S_IDLE     = 5'b00001, 
	S_COUNT    = 5'b00010, 
	S_FINISH   = 5'b00100, 
	S_ABORT    = 5'b01000,
	S_FINISH_2 = 5'b10000,
	S_UNDEF    = 5'bxxxxx
} State;


logic             active;
Reg_index         source;
Reg_index         target, target_ctr;
Reg_index         next_target_ctr;
State             state;
State             next_state;
Ls_cycle_counter  ls_ctr, next_ls_ctr;


always_comb
	unique case(data.inst.d.opcd)
		Op_lmw, Op_stmw:  active = 1'b1;
		default:          active = 1'b0;
	endcase


always_comb begin
	// default assignment
	next_ls_ctr = ls_ctr;

	if( active ) begin
		cw = '0;  // default assignment

		if( state == S_FINISH  || state == S_ABORT )
			cw.if_hold = 1'b0;
		else
			cw.if_hold = 1'b1;

		cw.alu_en = 1'b1;
		cw.ls_en = 1'b1;
		cw.read_gpr_a = (| data.inst.d.ra);  // RA != 0
		//cw.gpr_a = data.inst.d.ra;
		//cw.gpr_c = target;
		cw.if_gpr_c = source;
		cw.alu_op = Alu_add;
		cw.ls_mode = Load_word;

		if( (state == S_COUNT) || (state == S_FINISH) )
			cw.ls_multiple = 1'b1;

		if(  (!ctrl.hold && (state == S_IDLE)) || (state == S_COUNT) )
			cw.if_gpr_c_over = 1'b1;


		if( data.inst.d.opcd == Op_lmw ) begin
			// load variant
			cw.gpr_from_mem = target;
			if( (state != S_ABORT) && (ls_ctr == 0) )
				cw.write_gpr_from_mem = 1'b1;
		end else begin
			// store variant
			cw.read_gpr_c = 1'b1;
			if( (state != S_ABORT) && (state != S_FINISH) )
				cw.ls_we = 1'b1;
		end

		if( state == S_FINISH ) begin
			next_ls_ctr = LOAD_STORE_CYCLES;
		end else if( ls_ctr == 0 ) begin
			next_ls_ctr = LOAD_STORE_CYCLES;

			if( state == S_IDLE )
				cw.ls_first_cycle = 1'b1;
			else
				cw.ls_multiple_inc = 1'b1;
		end else begin
			next_ls_ctr = ls_ctr -1;
		end

	end else begin
		cw = '0;
	end
end

always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		target_ctr <= '0;
		state <= S_IDLE;
		ls_ctr <= LOAD_STORE_CYCLES;
	end else begin
		state <= next_state;
		target_ctr <= next_target_ctr;
		ls_ctr <= next_ls_ctr;
	end

always_comb
	unique case(state)
		S_IDLE: begin
			if( active && !ctrl.hold && (ls_ctr == 0) ) begin
				if( data.inst.d.rt == 31 )
					next_state = S_ABORT;
				//else if( data.inst.d.rt == 30 )
					//next_state = S_FINISH;
				else 
					next_state = S_COUNT;
			end else
				next_state = S_IDLE;
		end

		S_COUNT: begin
			if( !ctrl.hold && (target_ctr == {$bits(target_ctr){1'b1}}) && (ls_ctr == 0) )
				next_state = S_FINISH;
			else
				next_state = S_COUNT;
		end

		S_FINISH, S_ABORT:
			if( !ctrl.hold )
				next_state = S_IDLE;
			else
				next_state = state;

		default:
			next_state = S_UNDEF;
	endcase

always_comb begin
	if( (state == S_COUNT) && !ctrl.hold && (ls_ctr == 0) )
		next_target_ctr <= target_ctr + 1;
	else if( (state == S_COUNT) && (ctrl.hold || (ls_ctr != 0)) )
		next_target_ctr <= target_ctr;
	else if( ls_ctr == 0 )
		next_target_ctr <= data.inst.d.rt + 1;
	else if( (state == S_IDLE) && (ls_ctr != 0) )
		next_target_ctr <= data.inst.d.rt;
	else
		next_target_ctr <= target_ctr;
end


always_comb
	unique case(state)
		S_IDLE: begin
			target = data.inst.d.rt;
			source = next_target_ctr;
		end

		S_COUNT, S_FINISH, S_ABORT: begin
			target = target_ctr;
			source = next_target_ctr;
		end

		default: begin
			target = 'x;
			source = 'x;
		end
	endcase


endmodule
