// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Valu_simd_mult
  #(parameter width = 16, parameter no_confs = 3)
  ( input logic signed[width-1:0] a, b,
    input logic[$clog2(no_confs)-1:0] conf,
    output logic signed[2*width-1:0] res);

  `include "DW_dp_simd_mult_function.inc"

  assign res = DWF_dp_simd_mult_tc(a, b, conf);
endmodule

module Valu_simd_add
  #(parameter width = 16, parameter no_confs = 3)
  ( input logic signed[width-1:0] a, b,
    input logic[$clog2(no_confs)-1:0] conf,
    output logic signed[width-1:0] res);

  `include "DW_dp_simd_add_function.inc"

  assign res = DWF_dp_simd_add_tc(a, b, conf);
endmodule


module Valu_simd_mult_add
  #(parameter width = 16,
    parameter no_confs = 3,
    parameter num_stages = 2)
  ( input logic clk,
    input logic enable,
    input logic negate_b,
    input logic mult_shift,
    input logic shift_fractional,
    input Valu_pkg::Result_sel result_sel,
    input logic signed[width-1:0] a, b,
    input Valu_pkg::Valu_type conf,
    output logic signed[2*width-1:0] result);

  import Valu_pkg::*;


  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------

  typedef logic[width-1:0] Operand;
  typedef logic[2*width-1:0] Double_operand;
  typedef logic[(width/2)-1:0] Half_operand;
  typedef Half_operand[0:1] Halfs;
  

  //--------------------------------------------------------------------------------
  // Local functions 
  //--------------------------------------------------------------------------------

  /** Do sign extension depending on the vector configuration */
  function automatic Double_operand sign_extend(Operand x, Valu_type conf);
    Double_operand rv;
    Halfs halfs;

    halfs = Halfs'(x);

    unique case(conf)
      VALU_TYPE_FULL: rv = { {width{x[$left(x)]}}, x };
      VALU_TYPE_HALF: rv = {
        {$bits(Half_operand){halfs[0][$left(Half_operand)]}},
        halfs[0],
        {$bits(Half_operand){halfs[1][$left(Half_operand)]}},
        halfs[1]
      };
      default: rv = 'x;
    endcase

    return rv;
  endfunction


  function automatic Double_operand shift_left_saturating(Double_operand x,
      Valu_type conf);
    Double_operand rv;

    unique case(conf)
      VALU_TYPE_FULL:  begin
        if( (x[$left(x) -: 2] == 2'b01) )
          rv = { 1'b0, {2*width-1{1'b1}} };
        else
          rv = { x[$left(x)-1:$right(x)], 1'b0 };
      end

      VALU_TYPE_HALF: begin
        if( (x[2*width-1 -: 2] == 2'b01) )
          rv[2*width-1 -: width] = { 1'b0, {width-1{1'b1}} };
        else
          rv[2*width-1 -: width] = { x[2*width-2 : width], 1'b0 };

        if( (x[width-1 -: 2] == 2'b01) )
          rv[width-1 -: width] = { 1'b0, {width-1{1'b1}} };
        else
          rv[width-1 -: width] = { x[width-2 : 0], 1'b0 };
      end

      default: rv = 'x;
    endcase

    return rv;
  endfunction


  function automatic Double_operand shift_element_left_saturating(Double_operand x,
      Valu_type conf);
    Double_operand rv;

    if( conf == VALU_TYPE_FULL ) begin
      unique case(x[width -: 2])
        2'b10:       rv = { 1'b1, {2*width-1{1'b0}} };
        2'b01:       rv = { 1'b0, {2*width-1{1'b1}} };
        default:     rv = { x[width-1 : 0], {width{1'b0}} };
      endcase
    end else if( conf == VALU_TYPE_HALF ) begin
      unique case(x[width/2 -: 2])
        2'b10:       rv[width-1 : 0] = { 1'b1, {width-1{1'b0}} };
        2'b01:       rv[width-1 : 0] = { 1'b0, {width-1{1'b1}} };
        default:     rv[width-1 : 0] = { x[width/2 - 1 : 0], {width/2{1'b0}} };
      endcase

      unique case(x[2*width - width/2 -: 2])
        2'b10:       rv[2*width-1 : width] = { 1'b1, {width-1{1'b0}} };
        2'b01:       rv[2*width-1 : width] = { 1'b0, {width-1{1'b1}} };
        default:     rv[2*width-1 : width] = { x[2*width - width/2 - 1 : width], {width/2{1'b0}} };
      endcase
    end else begin
      rv = 'x;
    end

    return rv;
  endfunction




  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------

  Operand a_pipe[num_stages], a_d;
  Operand b_pipe[num_stages], b_d;
  Valu_type conf_pipe[num_stages], conf_d;
  logic negate_b_pipe[num_stages], negate_b_d;
  Result_sel result_sel_pipe[num_stages], result_sel_d;
  logic mult_shift_pipe[num_stages], mult_shift_d;
  logic shift_fractional_pipe[num_stages], shift_fractional_d;
  Double_operand a_ext, b_ext;
  Double_operand next_product;
  Double_operand next_result;
  Double_operand next_sum;
  logic[0:1] neg_ops;

  //--------------------------------------------------------------------------------
  // Datapath
  //--------------------------------------------------------------------------------

  always_ff @(posedge clk) begin : input_pipeline
    if( enable ) begin
      a_pipe[0] <= a;
      b_pipe[0] <= b;
      conf_pipe[0] <= conf;
      negate_b_pipe[0] <= negate_b;
      result_sel_pipe[0] <= result_sel;
      mult_shift_pipe[0] <= mult_shift;
      shift_fractional_pipe[0] <= shift_fractional;

      for(int i=1; i<num_stages; i++) begin
        a_pipe[i] <= a_pipe[i-1];
        b_pipe[i] <= b_pipe[i-1];
        conf_pipe[i] <= conf_pipe[i-1];
        negate_b_pipe[i] <= negate_b_pipe[i-1];
        result_sel_pipe[i] <= result_sel_pipe[i-1];
        mult_shift_pipe[i] <= mult_shift_pipe[i-1];
        shift_fractional_pipe[i] <= shift_fractional_pipe[i-1];
      end
    end
  end

  assign a_d = a_pipe[num_stages-1];
  assign b_d = b_pipe[num_stages-1];
  assign conf_d = conf_pipe[num_stages-1];
  assign negate_b_d = negate_b_pipe[num_stages-1];
  assign result_sel_d = result_sel_pipe[num_stages-1];
  assign mult_shift_d = mult_shift_pipe[num_stages-1];
  assign shift_fractional_d = shift_fractional_pipe[num_stages-1];


  always_comb begin
    // default assignments
    //b_ext = sign_extend(b[(NUM_ELEMS-i_elem) * ELEM_SIZE -1 -: ELEM_SIZE], ctrl.mult_conf);
    b_ext = sign_extend(b_d, conf_d);

    if( negate_b_d ) begin
      unique case(conf_d)
        VALU_TYPE_FULL: b_ext = (~sign_extend(b_d, VALU_TYPE_FULL)) + 1;
        VALU_TYPE_HALF: begin
          Double_operand tmp;
          tmp = sign_extend(b_d, VALU_TYPE_HALF);
          b_ext[2*width-1 -: width] = (~tmp[2*width-1 -: width]) + 1;
          b_ext[  width-1 -: width] = (~tmp[  width-1 -: width]) + 1;
        end
        default: b_ext = 'x;
      endcase
    end
  end

  assign a_ext = sign_extend(a_d, conf_d);


  always_comb begin
    // default assignments
    neg_ops = 2'b00;

    unique case(conf_d)
      VALU_TYPE_FULL: begin
        if( (a_d == {1'b1, {width-1{1'b0}}})
            && (b_ext == { {width+1{1'b1}}, {width-1{1'b0}}}) ) begin
          neg_ops = 2'b11;
        end
      end

      VALU_TYPE_HALF: begin
        if( (a_d[width-1 -: width/2] == {1'b1, {width/2-1{1'b0}}})
            && (b_ext[2*width-1 -: width] == { {width/2+1{1'b1}}, {width/2-1{1'b0}} }) )
          neg_ops[0] = 1'b1;

        if( (a_d[width/2-1 -: width/2] == {1'b1, {width/2-1{1'b0}}})
            && (b_ext[width-1 -: width] == { {width/2+1{1'b1}}, {width/2-1{1'b0}} }) )
          neg_ops[1] = 1'b1;
      end

      default:
        neg_ops = 2'bxx;
    endcase
  end


  Valu_simd_mult #(
    .width(width),
    .no_confs(no_confs)
  ) mult (
    .a(a_d),
    .b(b_d),
    .conf(conf_d),
    .res(next_product)
  );

  Valu_simd_add #(
    .width(2*width),
    .no_confs(no_confs)
  ) adder (
    .a(a_ext),
    .b(b_ext),
    .conf(conf_d),
    .res(next_sum)
  );

  always_comb 
    unique case(result_sel_d)
      RESULT_SEL_MUL: begin
        unique case({mult_shift_d, shift_fractional_d})
          2'b01:    next_result = shift_left_saturating(next_product, conf_d);
          2'b10:    next_result = shift_element_left_saturating(next_product, conf_d);
          default:  next_result = next_product;
        endcase
      end

      RESULT_SEL_ADD: begin
        if( mult_shift_d ) begin
          next_result = shift_element_left_saturating(next_sum, conf_d);

          unique case(conf_d)
            VALU_TYPE_FULL: begin
              if( neg_ops )
                next_result = { 1'b1, {2*width-1{1'b0}} };
            end

            VALU_TYPE_HALF: begin
              next_result = {
                neg_ops[0] ? { 1'b1, {width-1{1'b0}} } : next_result[2*width-1 -: width],
                neg_ops[1] ? { 1'b1, {width-1{1'b0}} } : next_result[  width-1 -: width]
              };
            end

            default: begin
              next_result = 'x;
            end
          endcase
        end else
          next_result = next_sum;
      end

      default: next_result = 'x;
    endcase


  assign result = next_result;



  //--------------------------------------------------------------------------------
  // Assertions
  //--------------------------------------------------------------------------------

`ifndef SYNTHESIS

  /**
   * Adding of full elements in saturating mode produces arithmetically correct results
   * when not saturating.
   */
  property full_add_no_overflows_is_correct;
    int a, b;

    @(posedge clk)
    ( ( ((result_sel_d == RESULT_SEL_ADD) 
          && (conf_d == VALU_TYPE_FULL)
          && mult_shift_d 
          && !negate_b_d),
          a = signed'(a_d),
          b = signed'(b_d))
    |-> ( !((a + b <= 2 ** (width-1)-1)
          && (a + b >= -2 ** (width-1)))
          || (next_result == (a + b) << width) ) );
  endproperty

  check_full_add_no_overflows_is_correct: assert property( full_add_no_overflows_is_correct );
  cover_full_add_no_overflows_is_correct: cover property( full_add_no_overflows_is_correct );


  /**
   * Adding of full elements in saturating mode saturates to the maximum or 
   * minimum representable value upon overflow.
   */
  property full_add_is_saturating;
    int a, b;

    @(posedge clk)
    ( ( ((result_sel_d == RESULT_SEL_ADD) 
          && (conf_d == VALU_TYPE_FULL)
          && mult_shift_d 
          && !negate_b_d),
          a = signed'(a_d),
          b = signed'(b_d))
    |-> ( ( !(a + b > 2 ** (width-1)-1) || (next_result == { 1'b0, {2*width-1{1'b1}} }) )
          && ( !(a + b < -2 ** (width-1)) || (next_result == { 1'b1, {2*width-1{1'b0}} }) ) ));
  endproperty

  check_full_add_is_saturating: assert property( full_add_is_saturating );
  cover_full_add_is_saturating: cover property( full_add_is_saturating );


`endif  /* SYNTHESIS */
endmodule

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
