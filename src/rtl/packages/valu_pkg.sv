// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


package Valu_pkg;

  typedef logic[3:0] Shift_range;

  typedef enum logic[1:0] {
    VALU_TYPE_FULL    = 2'b00,
    VALU_TYPE_HALF    = 2'b01,
    VALU_TYPE_QUARTER = 2'b10,
    VALU_TYPE_UNDEF   = 2'bxx
  } Valu_type;

  localparam int NUM_SUB_ELEMENT_CONFIGS = 3;

  typedef struct packed {
    logic mult;
    logic add;
    logic accumulate;
    logic scalar;
    Valu_type op_type;
  } Valu_operation;

  typedef enum logic[0:0] {
    ADD_IN_A_SEL_MULT = 1'b0,
    ADD_IN_A_SEL_A    = 1'b1
  } Add_in_a_sel;

  typedef enum logic[0:0] {
    ADD_IN_B_SEL_C = 1'b0,
    ADD_IN_B_SEL_G = 1'b1
  } Add_in_b_sel;

  typedef enum logic[1:0] {
    RESULT_SEL_ADD = 2'b01,
    RESULT_SEL_MUL = 2'b10
  } Result_sel;

  

endpackage
