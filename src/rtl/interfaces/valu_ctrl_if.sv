// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Valu_ctrl_if
  #(parameter int NUM_ELEMS = 8,
    /*parameter int ELEM_SIZE = 16,
    parameter int NUM_SUB_ELEMENT_CONFIGS = 3,
    parameter int SCALAR_SIZE = 32,*/
    parameter int MULT_STAGES = 1,
    parameter int ADD_STAGES = 1);
 
  import Valu_pkg::*;

  Valu_type mult_conf;
  Valu_type add_conf;
  Add_in_a_sel add_in_a_sel;
  Add_in_b_sel add_in_b_sel;
  logic mult_pipe_enable[0:MULT_STAGES-1];
  logic add_pipe_enable[0:ADD_STAGES-1];
  logic save_to_accum;
  Result_sel result_sel;
  Valu_type round_conf;
  logic saturate;
  logic mult_saturating;
  logic shift_fractional;
  Pu_inst::Fxv_cond cond;
  logic mult_by_one;
  logic mult_shift;
  logic add_to_zero;
  logic negate_b;
  logic stall;


  modport valu(
    input mult_conf, add_conf, add_in_a_sel, add_in_b_sel,
      mult_pipe_enable, add_pipe_enable, save_to_accum, result_sel,
      round_conf, saturate, mult_saturating, shift_fractional, cond,
      mult_by_one, mult_shift, add_to_zero, negate_b, stall
  );

  modport ctrl(
    output mult_conf, add_conf, add_in_a_sel, add_in_b_sel,
      mult_pipe_enable, add_pipe_enable, save_to_accum, result_sel,
      round_conf, saturate, mult_saturating, shift_fractional, cond,
      mult_by_one, mult_shift, add_to_zero, negate_b, stall
  );

endinterface
    


/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
