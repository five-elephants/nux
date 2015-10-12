// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Pu_types::Address;
import Pu_inst::Inst;
import Pu_interrupt::Int_ctrl_reg;

interface Pu_ctrl_if
  ( output logic sleep );
	// sleep modes and wakeup signals
	//logic sleep;
	logic wakeup;

	// external interrupt request signals
	logic doorbell;
	logic doorbell_ack;
	logic ext_input;
	logic ext_input_ack;
	logic other_ack;

	logic msr_ee;
	Int_ctrl_reg iccr;

	
	// monitoring
	Inst     mon_inst;
	Address  mon_pc;
	logic    mon_hold_dc;

	modport pu (
		output sleep, iccr, mon_inst, mon_pc, mon_hold_dc, msr_ee,
		input wakeup, doorbell, ext_input,
		output ext_input_ack, doorbell_ack, other_ack
	);

	modport ctrl (
		input sleep, iccr, mon_inst, mon_pc, mon_hold_dc, msr_ee,
		output wakeup, doorbell, ext_input,
		input ext_input_ack, doorbell_ack, other_ack
	);
endinterface
