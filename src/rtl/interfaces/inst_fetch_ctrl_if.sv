// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Pu_types::*;


interface Inst_fetch_ctrl_if;
	Address new_pc;
	Address int_vect;
	logic jump;
	logic int_jump;
	Freeze_at freeze_at;

	logic     gpr_sel_c_over;
	Reg_index gpr_sel_c;      // overrides selection from instruction word

	logic hold_data;
	logic hold_decode;
	logic hold;

  logic if_wait;  // go to the wait state

	assign hold = hold_data | hold_decode;

	modport decode(output hold_decode, gpr_sel_c, gpr_sel_c_over, if_wait);
	modport data_hazard_ctrl(output hold_data);
	modport inst_fetch(
		input new_pc, jump, hold, int_jump, int_vect, freeze_at,
		input gpr_sel_c, gpr_sel_c_over, if_wait
	);
	//modport write_back(output new_pc, jump);
	modport alu(output new_pc);
	modport branch(output jump);
	
	modport int_sched (
		output int_vect, int_jump, freeze_at
	);

endinterface
