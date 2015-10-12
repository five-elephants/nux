/* _use_m4_ macros
include(ops.m4)
*/

// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.




module Valu_ctrl
  #(parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int SCALAR_SIZE = 32,
    parameter int MULT_STAGES = 1,
    parameter int ADD_STAGES = 1)
  ( input logic clk, reset,
    input logic valid,
    input Pu_inst::Fxv_opcd xo,
    input Pu_inst::Fxv_cond cond,
    input logic stall,
    output logic result_avail,
    output logic ready,
    Valu_ctrl_if.ctrl ctrl );

  import Valu_pkg::*;
  import Pu_inst::*;

  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------
  
  Valu_type next_mult_conf, mult_conf;
  logic next_mult_by_one, mult_by_one;
  logic next_mult_shift, mult_shift;
  logic next_negate_b, negate_b;
  Valu_type next_add_conf, add_conf;
  Add_in_a_sel next_add_in_a_sel, add_in_a_sel;
  Add_in_b_sel next_add_in_b_sel, add_in_b_sel;
  logic next_add_to_zero, add_to_zero;
  Result_sel next_result_sel, result_sel;
  logic next_mult_pipe_enable, mult_pipe_enable;
  logic next_add_pipe_enable, add_pipe_enable;
  logic delayed_add_pipe_enable;
  logic mult_pipe_enable_shr[1:MULT_STAGES-1];
  logic add_pipe_enable_shr[1:ADD_STAGES-1];
  Valu_type next_round_conf, round_conf;
  logic next_saturate, saturate;
  logic next_shift_fractional, shift_fractional;
  logic next_save_to_accum, save_to_accum;
  Pu_inst::Fxv_cond cond_d;

  //--------------------------------------------------------------------------------
  // Control logic
  //--------------------------------------------------------------------------------

  assign ready = 1'b1;  // TODO

  always_comb begin : decode_configuration
    next_mult_conf = VALU_TYPE_FULL;
    next_add_conf = VALU_TYPE_FULL;
    next_round_conf = VALU_TYPE_FULL;

    if( valid ) begin
      unique casez( {Op_nve_xo, xo, 1'b0} )
        VECTOR_BYTE_OPS:
        begin
          next_mult_conf = VALU_TYPE_HALF;
          next_add_conf = VALU_TYPE_HALF;
          next_round_conf = VALU_TYPE_HALF;
        end

        default: begin
          next_mult_conf = VALU_TYPE_FULL;
          next_add_conf = VALU_TYPE_FULL;
          next_round_conf = VALU_TYPE_FULL;
        end
      endcase
    end
  end


  always_comb begin : decode_control_signals
    // default assignments 
    next_add_in_a_sel = ADD_IN_A_SEL_MULT;
    next_add_in_b_sel = ADD_IN_B_SEL_C;
    next_result_sel = RESULT_SEL_MUL;
    next_mult_pipe_enable = 1'b0;
    next_add_pipe_enable = 1'b0;
    next_saturate = 1'b0;
    next_shift_fractional = 1'b0;
    next_save_to_accum = 1'b0;
    next_mult_by_one = 1'b0;
    next_mult_shift = 1'b0;
    next_add_to_zero = 1'b0;
    next_negate_b = 1'b0;

    if( valid ) begin
      next_mult_pipe_enable = 1'b1;
      next_add_pipe_enable = 1'b1;

      unique case(xo)
        Pu_inst::Xop_fxvmtach,
        Pu_inst::Xop_fxvmtacb: begin
          next_mult_by_one = 1'b1;
          next_add_to_zero = 1'b1;
          next_save_to_accum = 1'b1;
        end

        Pu_inst::Xop_fxvmtachf,
        Pu_inst::Xop_fxvmtacbf: begin
          next_add_to_zero = 1'b1;
          next_save_to_accum = 1'b1;
          next_mult_by_one = 1'b1;
          next_mult_shift = 1'b1;
          //next_shift_fractional = 1'b1;
        end

        Pu_inst::Xop_fxvmahm,
        Pu_inst::Xop_fxvmabm: begin
        end

        Pu_inst::Xop_fxvmahfs,
        Pu_inst::Xop_fxvmabfs: begin
          next_saturate = 1'b1;
          next_shift_fractional = 1'b1;
        end

        Pu_inst::Xop_fxvmatachm,
        Pu_inst::Xop_fxvmatacbm: begin
          next_save_to_accum = 1'b1;
        end

        Pu_inst::Xop_fxvmatachfs,
        Pu_inst::Xop_fxvmatacbfs: begin
          next_save_to_accum = 1'b1;
          next_saturate = 1'b1;
          next_shift_fractional = 1'b1;
        end

        Pu_inst::Xop_fxvmulhm,
        Pu_inst::Xop_fxvmulbm: begin
          next_add_to_zero = 1'b1;
        end

        Pu_inst::Xop_fxvmulhfs,
        Pu_inst::Xop_fxvmulbfs: begin
          next_add_to_zero = 1'b1;
          next_saturate = 1'b1;
          next_shift_fractional = 1'b1;
        end

        Pu_inst::Xop_fxvmultachm,
        Pu_inst::Xop_fxvmultacbm: begin
          next_add_to_zero = 1'b1;
          next_save_to_accum = 1'b1;
        end

        Pu_inst::Xop_fxvmultachfs,
        Pu_inst::Xop_fxvmultacbfs: begin
          next_add_to_zero = 1'b1;
          next_save_to_accum = 1'b1;
          next_saturate = 1'b1;
          next_shift_fractional = 1'b1;
        end

        Pu_inst::Xop_fxvaddhm,
        Pu_inst::Xop_fxvaddbm: begin
          next_add_to_zero = 1'b1;
          next_result_sel = RESULT_SEL_ADD;
        end

        Pu_inst::Xop_fxvaddhfs,
        Pu_inst::Xop_fxvaddbfs: begin
          next_add_to_zero = 1'b1;
          next_result_sel = RESULT_SEL_ADD;
          next_saturate = 1'b1;
          next_mult_shift = 1'b1;
        end

        Pu_inst::Xop_fxvaddtachm,
        Pu_inst::Xop_fxvaddtacb: begin
          next_result_sel = RESULT_SEL_ADD;
          next_add_to_zero = 1'b1;
          next_save_to_accum = 1'b1;
        end

        Pu_inst::Xop_fxvaddachm,
        Pu_inst::Xop_fxvaddacbm: begin
          next_mult_by_one = 1'b1;
        end

        Pu_inst::Xop_fxvaddachfs,
        Pu_inst::Xop_fxvaddacbfs: begin
          next_mult_by_one = 1'b1;
          next_saturate = 1'b1;
          next_mult_shift = 1'b1;
        end

        Pu_inst::Xop_fxvaddactachm,
        Pu_inst::Xop_fxvaddactacb: begin
          next_mult_by_one = 1'b1;
          next_save_to_accum = 1'b1;
        end

        Pu_inst::Xop_fxvaddactachf,
        Pu_inst::Xop_fxvaddactacbf: begin
          next_mult_by_one = 1'b1;
          next_save_to_accum = 1'b1;
          next_mult_shift = 1'b1;
          next_saturate = 1'b1;
        end

        Pu_inst::Xop_fxvsubhm,
        Pu_inst::Xop_fxvsubbm: begin
          next_negate_b = 1'b1;
          next_add_to_zero = 1'b1;
          next_result_sel = RESULT_SEL_ADD;
        end

        Pu_inst::Xop_fxvsubhfs,
        Pu_inst::Xop_fxvsubbfs: begin
          next_negate_b = 1'b1;
          next_add_to_zero = 1'b1;
          next_result_sel = RESULT_SEL_ADD;
          next_saturate = 1'b1;
          next_mult_shift = 1'b1;
        end

        default: begin
        end
      endcase
    end
  end

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      mult_conf <= VALU_TYPE_FULL;
      add_conf <= VALU_TYPE_FULL;
      add_in_a_sel <= ADD_IN_A_SEL_MULT;
      add_in_b_sel <= ADD_IN_B_SEL_C;
      result_sel <= RESULT_SEL_MUL;
      mult_pipe_enable <= 1'b0;
      add_pipe_enable <= 1'b0;
      round_conf <= VALU_TYPE_FULL;
      save_to_accum <= 1'b0;
      mult_by_one <= 1'b0;
      mult_shift <= 1'b0;
      add_to_zero <= 1'b0;
      negate_b <= 1'b0;
      saturate <= 1'b0;
      shift_fractional <= 1'b0;
    end else begin
      if( !stall ) begin
        mult_conf <= next_mult_conf;
        add_conf <= next_add_conf;
        add_in_a_sel <= next_add_in_a_sel;
        add_in_b_sel <= next_add_in_b_sel;
        result_sel <= next_result_sel;
        mult_pipe_enable <= next_mult_pipe_enable;
        add_pipe_enable <= next_add_pipe_enable;
        round_conf <= next_round_conf;
        save_to_accum <= next_save_to_accum;
        cond_d <= cond;
        mult_by_one <= next_mult_by_one;
        mult_shift <= next_mult_shift;
        add_to_zero <= next_add_to_zero;
        negate_b <= next_negate_b;
        saturate <= next_saturate;
        shift_fractional <= next_shift_fractional;
      end
    end

  // delay control signals to match datapath
  // immediate:
  assign
    ctrl.mult_conf = mult_conf,
    ctrl.mult_by_one = mult_by_one,
    ctrl.mult_shift = mult_shift,
    ctrl.negate_b = negate_b,
    ctrl.cond = cond_d,
    ctrl.result_sel = result_sel,
    ctrl.stall = stall,
    ctrl.mult_saturating = saturate,
    ctrl.shift_fractional = shift_fractional;

  // after multiplier
  Shift_reg #(
    .depth(MULT_STAGES),
    .width($bits(add_conf)
        +$bits(add_in_a_sel)
        +$bits(add_in_b_sel)
        +$bits(add_to_zero))
  ) shift_after_mul (
    .clk,
    .reset,
    .en(~stall),
    .in({add_conf, add_in_a_sel, add_in_b_sel, add_to_zero}),
    .out({ctrl.add_conf, ctrl.add_in_a_sel, ctrl.add_in_b_sel, ctrl.add_to_zero})
  );

  // after adder
  Shift_reg #(
    .depth(MULT_STAGES+ADD_STAGES),
    .width($bits(round_conf)
        +$bits(saturate)
        +$bits(save_to_accum))
  ) shift_after_add (
    .clk,
    .reset,
    .en(~stall),
    .in({round_conf, saturate, save_to_accum}),
    .out({ctrl.round_conf, ctrl.saturate, ctrl.save_to_accum})
  );

  // shift register for multiplier and adder output pipeline enables
  //always_ff @(posedge clk) begin : shift_mult_enables
    //if( reset ) begin
      //for(int i=$left(mult_pipe_enable_shr); i<=$right(mult_pipe_enable_shr); i++)
        //mult_pipe_enable_shr[i] <= 1'b0;
    //end else begin
      //if( !stall ) begin
        //mult_pipe_enable_shr[$left(mult_pipe_enable_shr)] <= mult_pipe_enable;

        //for(int i=$left(mult_pipe_enable_shr)+1; i<=$right(mult_pipe_enable_shr); i++)
          //mult_pipe_enable_shr[i] <= mult_pipe_enable_shr[i-1];
      //end
    //end
  //end

  //always_comb begin
    //ctrl.mult_pipe_enable[0] = mult_pipe_enable;

    //for(int i=1; i<=$right(ctrl.mult_pipe_enable); i++)
      //ctrl.mult_pipe_enable[i] = mult_pipe_enable_shr[i];
  //end
  always_comb begin
    ctrl.mult_pipe_enable[0] = ~stall;

    for(int i=$left(ctrl.mult_pipe_enable)+1; i<=$right(ctrl.mult_pipe_enable); i++)
      ctrl.mult_pipe_enable[i] = 1'b0;
  end


  Shift_reg #(
    .depth(MULT_STAGES-1),
    .width(1)
  ) shift_adder_enable (
    .clk,
    .reset,
    .en(~stall),
    .in(add_pipe_enable),
    .out(delayed_add_pipe_enable)
  );

  always_ff @(posedge clk) begin : shift_add_enables
    if( reset ) begin
      for(int i=$left(ctrl.add_pipe_enable); i<=$right(ctrl.add_pipe_enable); i++)
        ctrl.add_pipe_enable[i] <= 1'b0;
    end else begin
      if( !stall ) begin
        ctrl.add_pipe_enable[0] <= delayed_add_pipe_enable;

        for(int i=$left(ctrl.add_pipe_enable)+1; i<=$right(ctrl.add_pipe_enable); i++)
          ctrl.add_pipe_enable[i] <= ctrl.add_pipe_enable[i-1];
      end
    end
  end
  

  //--------------------------------------------------------------------------------
  Shift_reg #(
    .depth(MULT_STAGES+ADD_STAGES+1),
    .width(1)
  ) shift_result_avail (
    .clk,
    .reset,
    .en(~stall),
    .in(valid),
    .out(result_avail)
  );

  //--------------------------------------------------------------------------------
  // Coverage
  //--------------------------------------------------------------------------------
 
`ifndef SYNTHESIS

  //covergroup cg_op @(posedge clk);
    //mult: coverpoint op.mult iff(!reset && valid) {
      //option.weight = 0;
    //}
    //add: coverpoint op.add iff(!reset && valid) {
      //option.weight = 0;
    //}
    //scalar: coverpoint op.scalar iff(!reset && valid) {
      //option.weight = 0;
    //}
    //op_type: coverpoint op.op_type iff(!reset && valid) {
      //option.weight = 0;
    //}

    //cross mult, add, scalar, op_type;
  //endgroup

  //cg_op cg_op_inst = new();

`endif  /* SYNTHESIS */

endmodule

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
