// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** m4 macros
* include(ops.m4)
* */

/** Decode module for multiply and divide instructions */
module Dec_mul_div
	(	input logic                  clk, reset,
		Decode_ctrl_if.decode        ctrl,
		Decode_data_if.decode        data,
		Fixedpoint_ctrl_if.feedback  fxdp_fb,

		output Control_word          cw
	);

import Pu_types::*;
import Pu_inst::*;

logic active;
logic read_cmplt;      

//---------------------------------------------------------------------------
always_comb begin
	logic[14:0] cop;

	cop = {data.inst.xo.opcd, data.inst.xo.xo};
	unique casez(cop)
		{Op_mulli, 9'bz},
		{Op_alu_xo, Xop_mulhw},
		{Op_alu_xo, Xop_mullw},
		{Op_alu_xo, Xop_mulhwu},
		{Op_alu_xo, Xop_divw},
		{Op_alu_xo, Xop_divwu}:
			active = 1'b1;

		default:
			active = 1'b0;
	endcase
end
//---------------------------------------------------------------------------

always_comb 
	if( active ) begin
		logic[14:0] cop;

		// default assignment
		cw = {$bits(cw){1'b0}};

		cop = {data.inst.xo.opcd, data.inst.xo.xo};
		case(cop)
			{Op_alu_xo, Xop_mulhwu}: begin
				cw.mul_high = 1'b1;
				cw.mul_unsigned = 1'b1;
			end

			{Op_alu_xo, Xop_mulhw}: begin
				cw.mul_high = 1'b1;
			end

			{Op_alu_xo, Xop_divwu}: begin
				cw.div_unsigned = 1'b1;
			end
		endcase

		cw.read_gpr_a = ~read_cmplt; 
		cw.read_gpr_b = ~read_cmplt; 
		//cw.gpr_a = data.inst.xo.ra;
		//cw.gpr_b = data.inst.xo.rb;
		cw.gpr_from_alu = data.inst.xo.rt;

		if( !ctrl.hold ) begin
			unique case(cop)
				{Op_alu_xo, Xop_divw},
				{Op_alu_xo, Xop_divwu}:
					cw.fxdp_sel = Fu_div;

				default:
					cw.fxdp_sel = Fu_mul;
			endcase
		end

		if( fxdp_fb.mul_complete | fxdp_fb.div_complete ) begin
			cw.write_gpr_from_alu = 1'b1;
			cw.if_hold = 1'b0;

			if( data.inst.xo.opcd == Op_mulli ) begin
				cw.wb_record_cr = '0;
				cw.write_cr = '0;
			end else begin
				cw.wb_record_cr = {7'b0, data.inst.xo.rc};
				cw.write_cr = {7'b0, data.inst.xo.rc};
			end

			if( (data.inst.xo.opcd == Op_alu_xo 
				&& (data.inst.xo.xo == Xop_mullw
					|| data.inst.xo.xo == Xop_divw
					|| data.inst.xo.xo == Xop_divwu)) )
				cw.wb_record_ov = data.inst.xo.oe;
		end else begin
			cw.if_hold = 1'b1;
			cw.write_gpr_from_alu = 1'b0;
		end
		
	end else begin
		cw = {$bits(cw){1'b0}};
	end

//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
	if( reset )
		read_cmplt <= 1'b0;
	else
		if( fxdp_fb.mul_complete | fxdp_fb.div_complete )
			read_cmplt <= 1'b0;
		else
			read_cmplt <= (active & !ctrl.hold) | read_cmplt;

//---------------------------------------------------------------------------

endmodule
