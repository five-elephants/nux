// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Branch_hazard_ctrl
	#(	parameter logic[2:0] BRANCH_HOLD_TIME = 3'd3 )
	(	input logic clk,
		input logic reset,

		Branch_hazard_ctrl_if.branch_hazard_ctrl  ctrl,
		Decode_ctrl_if.branch_hazard_ctrl         decode,
		Inst_fetch_ctrl_if.branch_hazard_ctrl     inst_fetch,
		Data_hazard_ctrl_if.branch_hazard_ctrl    data_hazard );

import Pu_types::*;
import Pu_inst::*;

logic      jump_detected;
logic[2:0] hold_ctr;


//---------------------------------------------------------------------------
// Detect a branch (and predict its outcome)
//---------------------------------------------------------------------------
always_comb
begin
	unique case(ctrl.inst.d.opcd)
		Op_branch:  jump_detected = 1'b1;
		Op_bc:      jump_detected = 1'b1;
		Op_bclr:    jump_detected = 1'b1;
		default:    jump_detected = 1'b0;
	endcase
end


//---------------------------------------------------------------------------
// Stall the pipeline until the new PC has been loaded
//---------------------------------------------------------------------------
always_ff @(posedge clk or posedge reset)
begin
	if( reset )
		hold_ctr <= 0;
	else begin
		
		if( hold_ctr > 0 )
			hold_ctr <= hold_ctr - 1;

		if( jump_detected && !inst_fetch.hold )
			hold_ctr <= BRANCH_HOLD_TIME;
		
	end
end

always_comb
	if( hold_ctr == 0 ) begin
		decode.hold_branch = 1'b0;
		inst_fetch.hold_branch = 1'b0;
		data_hazard.en = 1'b1;
	end else begin
		decode.hold_branch = 1'b1;
		inst_fetch.hold_branch = 1'b1;
		data_hazard.en = 1'b0;
	end

// // hold as long as counter is not zero
// always_comb 
// 	if( hold_ctr == 0 ) hold = 1'b0; 
// 	else hold = 1'b1;
// 
// 
// assign inst_fetch.hold_branch = hold;
// 
// always_ff @(posedge clk or posedge reset)
// 	if( reset )
// 		decode.hold_branch <= 1'b0;
// 	else
// 		decode.hold_branch <= hold;


endmodule
