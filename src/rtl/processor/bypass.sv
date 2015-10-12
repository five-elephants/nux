// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Bypass
	#(	parameter bit ENABLE_FORWARDING = 1'b1 )
	(	Bypass_if.bypass           ctrl,
		//Alu_data_if.bypass         alu,
		//Branch_data_if.bypass      branch,
		Fixedpoint_data_if.bypass  fixedpoint,
		Load_store_data_if.bypass  load_store,
		Write_back_data_if.bypass  write_back );

import Pu_types::*;

//---------------------------------------------------------------------------
generate
if( ENABLE_FORWARDING ) begin : gen_forwarding
	
	always_comb
	begin
		// forward to ALU a
		// fxdp to alu must have priority over ls to alu, because of WAW hazards
		if( ctrl.lines.fxdp_to_alu_a )
			fixedpoint.alu_a_out = fixedpoint.res;
		//else if( ctrl.lines.ls_to_alu_a )
			//fixedpoint.alu_a_out = write_back.dout;
		else
			fixedpoint.alu_a_out = fixedpoint.alu_a_in;

		// forward to ALU b
		if( ctrl.lines.fxdp_to_alu_b )
			fixedpoint.alu_b_out = fixedpoint.res;
		//else if( ctrl.lines.ls_to_alu_b )
			//fixedpoint.alu_b_out = write_back.dout;
		else
			fixedpoint.alu_b_out = fixedpoint.alu_b_in;
	end

	// TODO implement forwarding lines

	//assign
		////fixedpoint.alu_a_out = fixedpoint.alu_a_in,
		////fixedpoint.alu_b_out = fixedpoint.alu_b_in,
		//fixedpoint.alu_cr_out = fixedpoint.alu_cr_in,
		//fixedpoint.rotm_x_out = fixedpoint.rotm_x_in,
		//fixedpoint.spreu_a_out = fixepdoint.spreu_a_in,
		//fixedpoint.spreu_cr_out = fixedpoint.spreu_cr_in,
		//fixedpoint.mul_a_out = fixedpoint.mul_a_in,
		//fixedpoint.mul_b_out = fixedpoint.mul_b_in,
		//fixedpoint.div_a_out = fixedpoint.div_a_in,
		//fixedpoint.div_b_out = fixedpoint.div_b_in;

	// WARNING! input lines are shorted to alu inputs!
	assign
		fixedpoint.alu_cr_out = fixedpoint.alu_cr_in,
		fixedpoint.rotm_x_out = fixedpoint.alu_a_out,
		fixedpoint.rotm_q_out = fixedpoint.alu_b_out,
		fixedpoint.spreu_a_out = fixedpoint.alu_a_out,
		fixedpoint.spreu_cr_out = fixedpoint.alu_cr_out,
		fixedpoint.mul_a_out = fixedpoint.alu_a_out,
		fixedpoint.mul_b_out = fixedpoint.alu_b_out,
		fixedpoint.div_a_out = fixedpoint.alu_a_out,
		fixedpoint.div_b_out = fixedpoint.alu_b_out;
		

	assign
		load_store.bp_din = load_store.ls_din;

end : gen_forwarding
//---------------------------------------------------------------------------
else
//---------------------------------------------------------------------------
begin : gen_no_forwarding
	assign
		fixedpoint.alu_a_out = fixedpoint.alu_a_in,
		fixedpoint.alu_b_out = fixedpoint.alu_b_in,
		fixedpoint.alu_cr_out = fixedpoint.alu_cr_in,
		fixedpoint.rotm_x_out = fixedpoint.rotm_x_in,
		fixedpoint.rotm_q_out = fixedpoint.rotm_q_in,
		fixedpoint.spreu_a_out = fixedpoint.spreu_a_in,
		fixedpoint.spreu_cr_out = fixedpoint.spreu_cr_in,
		fixedpoint.mul_a_out = fixedpoint.mul_a_in,
		fixedpoint.mul_b_out = fixedpoint.mul_b_in,
		fixedpoint.div_a_out = fixedpoint.div_a_in,
		fixedpoint.div_b_out = fixedpoint.div_b_in;

	assign
		load_store.bp_din = load_store.ls_din;
end : gen_no_forwarding
//---------------------------------------------------------------------------
endgenerate


endmodule
