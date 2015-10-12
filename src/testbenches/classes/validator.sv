// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef VALIDATOR__
`define VALIDATOR__

`include "predictor.sv"
`include "instruction_loader.sv"

class Validator;
	Predictor          pred;
	Instruction_loader loader;
	State              exp_state;
	Cmp_ignore_mask    compare_mask;

	extern function new(input Predictor pr, Instruction_loader load);

	extern virtual function void validate_start(input Instruction inst, State state);
	extern virtual function int wait_time(input Instruction inst);
	extern virtual function bit  validate_end();

	extern virtual function Cmp_ignore_mask get_compare_mask(input Instruction inst);
endclass

//---------------------------------------------------------------------------
function
Validator::new(input Predictor pr, Instruction_loader load);
	pred = pr;
	loader = load;
endfunction
//---------------------------------------------------------------------------
function void 
Validator::validate_start(input Instruction inst, State state);
	exp_state = pred.predict(inst, state);
	loader.load(inst, state);

	compare_mask = get_compare_mask(inst);
endfunction
//---------------------------------------------------------------------------
function int
Validator::wait_time(input Instruction inst);
	Inst i;
	logic[15:0] cop;
	int rv;

	i = inst.get();
	cop = {i.x.opcd, i.x.xo};
	casez(cop)
		{Op_lwzu, 10'bz}, {Op_lbzu, 10'bz}, {Op_lhzu, 10'bz},
		{Op_alu_xo, Xop_lbzux}, {Op_alu_xo, Xop_lhzux}, {Op_alu_xo, Xop_lwzux}:
			rv = 3;

		{Op_alu_xo, 1'bz, Xop_mulhwu},
		{Op_alu_xo, 1'bz, Xop_mulhw},
		{Op_alu_xo, 1'bz, Xop_mullw},
		{Op_mulli, 10'bz}:
			rv = 19;  // the sequential DW multiplier needs about 30 cycles 
			          // for initialization plus the same amount for execution

		{Op_alu_xo, 1'bz, Xop_divw},
		{Op_alu_xo, 1'bz, Xop_divwu}:
			rv = 67;

		{Op_lmw, 10'bz}, {Op_stmw, 10'bz}:
			rv = 34;

		default:
			rv = 3;
	endcase

	return rv;
endfunction
//---------------------------------------------------------------------------
function bit
Validator::validate_end();
	State res_state = loader.get_state();
	return compare_state_masked(exp_state, res_state, compare_mask);
endfunction
//---------------------------------------------------------------------------
function Cmp_ignore_mask
Validator::get_compare_mask(input Instruction inst);
	Inst op = inst.get();
	Cmp_ignore_mask rv;
	logic[15:0] cop;

	rv.pc = 1'b1;
	for(int i=0; i<32; i++) rv.gpr[i] = 1'b0;
	for(int i=0; i<8; i++) rv.cr[i] = 1'b0;
	rv.ctr = 1'b0;
	rv.lnk = 1'b0;
	rv.xer = 1'b0;
	rv.srr0 = 1'b0;
	rv.srr1 = 1'b0;
	rv.csrr0 = 1'b0;
	rv.csrr1 = 1'b0;
	rv.mcsrr0 = 1'b0;
	rv.mcsrr1 = 1'b0;
	rv.msr = 1'b0;
	rv.esr = 1'b0;
	rv.dear = 1'b1;  // TODO enable as soon as it is used
	rv.gout = 1'b0;
	rv.mem = 1'b1;
	rv.nve_sstate = 1'b0;
	rv.nve_lut = 1'b0;

	cop = {op.x.opcd, op.x.xo};
	casez(cop)
		{Op_branch, 10'bz}, {Op_bc, 10'bz}, {Op_bclr, 10'bz}:
		begin
			rv.pc = 1'b1;  // TODO enable PC calculation in predictor model
		end
		
		{Op_stw, 10'bz}, {Op_lwz, 10'bz}, {Op_sth, 10'bz},
		{Op_stb, 10'bz}, {Op_lhz, 10'bz}, {Op_lbz, 10'bz},
		{Op_stwu, 10'bz}, {Op_sthu, 10'bz}, {Op_stbu, 10'bz},
		{Op_lwzu, 10'bz}, {Op_lhzu, 10'bz}, {Op_lbzu, 10'bz},
		{Op_alu_xo, Xop_stwx}, {Op_alu_xo, Xop_stwux},
		{Op_alu_xo, Xop_sthx}, {Op_alu_xo, Xop_sthux},
		{Op_alu_xo, Xop_stbx}, {Op_alu_xo, Xop_stbux},
		{Op_alu_xo, Xop_lwzx}, {Op_alu_xo, Xop_lwzux},
		{Op_alu_xo, Xop_lhzx}, {Op_alu_xo, Xop_lhzux},
		{Op_alu_xo, Xop_lbzx}, {Op_alu_xo, Xop_lbzux}:
		begin
			rv.mem = 1'b0;
			rv.srr0 = 1'b1;  // instructions may cause alignment interrupts
			rv.srr1 = 1'b1;  // I don't predict that
			rv.msr = 1'b1;
			rv.esr = 1'b1;
		end

		{Op_alu_xo, Xop_tw}, {Op_twi, 10'bz}:
		begin
			rv.srr0 = 1'b1;  // PC doesn't realy have a meaning in SIT
		end
	endcase

	return rv;
endfunction
//---------------------------------------------------------------------------

`endif
