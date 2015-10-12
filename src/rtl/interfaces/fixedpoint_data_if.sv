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

interface Fixedpoint_data_if;
	// ALU input
	Word        alu_a_in, alu_a_out;
	Word        alu_b_in, alu_b_out;
	logic       alu_cin;
	Word        alu_cr_in, alu_cr_out;   // Condition_register not supported by synplify

	// rotate and mask input
	Word        rotm_x_in, rotm_x_out;
	Word        rotm_q_in, rotm_q_out;
	logic[4:0]  rotm_sh;
	logic[4:0]  rotm_ma;
	logic[4:0]  rotm_mb;

	// Special purpose register execution unit
	Word        spreu_cr_in, spreu_cr_out;
	Word        spreu_a_in, spreu_a_out;
	Word        spreu_sprin;
	Msr         spreu_msrin;

	// Multiplier
	Word        mul_a_in, mul_a_out;
	Word        mul_b_in, mul_b_out;

	// Divider
	Word        div_a_in, div_a_out;
	Word        div_b_in, div_b_out;

	// results of the execute stage for the bypass network
	Word        alu_res;
	Word        rotm_res;
	Word        spreu_res;
	Word        mul_res;
	Word        div_res;
	Word        res;  // intermediate result for bypassing

  assign
    alu_a_out = alu_a_in,
    alu_b_out = alu_b_in,
    alu_cr_out = alu_cr_in,
    rotm_x_out = rotm_x_in,
    rotm_q_out = rotm_q_in,
    spreu_cr_out = spreu_cr_in,
    spreu_a_out = spreu_a_in,
    mul_a_out = mul_a_in,
    mul_b_out = mul_b_in,
    div_a_out = div_a_in,
    div_b_out = div_b_in;


	modport op_fetch
		(	//import set_zero,
			output alu_a_in,
			output alu_b_in,
			output alu_cin,
			output alu_cr_in,
			output rotm_x_in,
			output rotm_q_in,
			output rotm_sh, rotm_ma, rotm_mb,
			output spreu_a_in,
			output spreu_cr_in,
			output spreu_sprin,
			output spreu_msrin,
			output mul_a_in,
			output mul_b_in,
			output div_a_in,
			output div_b_in );

	modport execute
		(	input alu_a_out,
			input alu_b_out,
			input alu_cin,
			input alu_cr_out,
			input rotm_x_out,
			input rotm_q_out,
			input rotm_sh, rotm_ma, rotm_mb,
			input spreu_a_out,
			input spreu_cr_out,
			input spreu_sprin,
			input spreu_msrin,
			input mul_a_out,
			input mul_b_out,
			input div_a_out,
			input div_b_out,
			output res);


	modport bypass
		(	input alu_a_in, alu_b_in, alu_cr_in,
			rotm_x_in, rotm_q_in,
			spreu_a_in, spreu_cr_in, 
			mul_a_in, mul_b_in, 
			div_a_in, div_b_in, 
			output alu_a_out, alu_b_out, alu_cr_out,
			rotm_x_out, rotm_q_out,
			spreu_a_out, spreu_cr_out,
			mul_a_out, mul_b_out,
			div_a_out, div_b_out,
			
			input res );


endinterface
