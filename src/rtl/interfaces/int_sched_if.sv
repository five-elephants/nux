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
import Pu_interrupt::*;

/** Interface for the interrupt scheduler */
interface Int_sched_if
	( input logic clk, reset );

	//---------------------------------------------------------------------------
	// Signals
	//---------------------------------------------------------------------------
	//Except_mcheck   mcheck;
	//Except_critical critical;
	//Except_base     base;
	logic mcheck_mcheck;

	logic critical_cinput;
	logic critical_cdoorbell;

	logic base_ext_input;
	logic base_ext_input_ack;
	logic base_alignment;
	logic base_illegal;
	logic base_trap;
	logic base_unimplemented;
	logic base_doorbell;
	logic base_doorbell_ack;

	logic other_ack;

	Address         pc;
	Address         pc_alignment;
	Address         pc_trap;

	logic           rest_base, rest_base_d, rest_base_d2, rest_base_wb;
	logic           rest_crit, rest_crit_d, rest_crit_d2, rest_crit_wb;
	logic           rest_mcheck, rest_mcheck_d, rest_mcheck_d2, rest_mcheck_wb;

	logic           block_external;   // block external interrupts
	logic           block;            // block all interrupts

	//always_ff @(posedge clk or posedge reset)
		//if( reset ) begin
			//rest_base_d <= 1'b0;
			//rest_base_d2 <= 1'b0;
			//rest_crit_d <= 1'b0;
			//rest_crit_d2 <= 1'b0;
			//rest_mcheck_d <= 1'b0;
			//rest_mcheck_d2 <= 1'b0;
		//end else begin
			//if( !dis_ex ) begin
				//rest_base_d <= rest_base;
				//rest_crit_d <= rest_crit;
				//rest_mcheck_d <= rest_mcheck;
			//end else begin
				//rest_base_d <= 1'b0;
				//rest_crit_d <= 1'b0;
				//rest_mcheck_d <= 1'b0;
			//end

			//if( !dis_ls ) begin
				//rest_base_d2 <= rest_base_d;
				//rest_crit_d2 <= rest_crit_d;
				//rest_mcheck_d2 <= rest_mcheck_d;
			//end else begin
				//rest_base_d2 <= 1'b0;
				//rest_crit_d2 <= 1'b0;
				//rest_mcheck_d2 <= 1'b0;
			//end
		//end

	//assign
		//rest_base_wb = rest_base_d2 & ~dis_wb,
		//rest_crit_wb = rest_crit_d2 & ~dis_wb,
		//rest_mcheck_wb = rest_mcheck_d2 & ~dis_wb;
	assign
		rest_base_wb = rest_base,
		rest_crit_wb = rest_crit,
		rest_mcheck_wb = rest_mcheck;

	//---------------------------------------------------------------------------
	// modports
	//---------------------------------------------------------------------------
	modport p_mcheck ( output mcheck_mcheck );
	modport p_critical ( output critical_cinput, critical_cdoorbell );
	modport p_base ( 
		output base_ext_input, base_alignment, base_illegal, base_trap,
			base_unimplemented, base_doorbell,
		input base_ext_input_ack, base_doorbell_ack, other_ack
	);

	//modport inst_fetch ( 
		//output pc, speculative, spec_inval, tran_ip, dis_ex, dis_ls, dis_wb
	//);
	//modport decode ( 
		//output rest_base, rest_crit, rest_mcheck,
			//block_external
	//);
	modport frontend ( output block_external, pc, block );
	modport load_store ( output base_alignment, pc_alignment );
	modport trap ( output base_trap, pc_trap, rest_base, rest_crit, rest_mcheck );
	modport int_sched ( 
		input pc, rest_base_wb, rest_crit_wb, rest_mcheck_wb,
			block_external, block,
		input mcheck_mcheck, critical_cinput, critical_cdoorbell,
		input base_ext_input, base_alignment, base_illegal, base_trap,
			base_unimplemented, base_doorbell,
		output base_ext_input_ack, base_doorbell_ack, other_ack,
		input pc_alignment, pc_trap
	);
endinterface
