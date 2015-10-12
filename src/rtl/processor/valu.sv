// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Vector ALU with fixed-point multiplier and adder
 * 
 * This module works on vectors of size NUM_ELEMS*ELEM_SIZE bits. Each element 
 * can be further sub-partitioned into NUM_SUB_ELEMENTS_CONFIGS parts by halfing the
 * element succsessively.
 */
module Valu
  #(parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int ENABLES_PER_ELEMENT = 4,
    parameter int SCALAR_SIZE = 32,
    parameter int MULT_STAGES = 1,
    parameter int ADD_STAGES = 1)
  ( input logic clk, reset,
    Valu_ctrl_if.valu ctrl,
    input Vector::Compare[0:NUM_ELEMS-1] vcr,
    input logic[NUM_ELEMS*ELEM_SIZE-1:0] a,
    input logic[NUM_ELEMS*ELEM_SIZE-1:0] b,
    input logic[SCALAR_SIZE-1:0] g,
    output logic[NUM_ELEMS*ELEM_SIZE-1:0] y,
    output logic[0:ENABLES_PER_ELEMENT-1] write_mask[0:NUM_ELEMS-1] );

  import Valu_pkg::*;

  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------

  typedef logic[(2*ELEM_SIZE)-1:0] Vector_double_element;
  typedef logic[ELEM_SIZE-1:0] Vector_element;
  typedef logic[ELEM_SIZE/2-1:0] Vector_half_element;
  typedef logic[ELEM_SIZE/4-1:0] Vector_quarter_element;
  typedef Vector_double_element Double_vector_elems[0:NUM_ELEMS-1];
  typedef Vector_element Vector_elems[0:NUM_ELEMS-1];
  typedef logic[NUM_ELEMS*ELEM_SIZE-1:0] Vector_raw;
  typedef logic[SCALAR_SIZE-1:0] Scalar;
  typedef Vector_half_element[0:1] Vector_element_halfs;
  typedef Vector_quarter_element[0:3] Vector_element_quarters;

  typedef logic[0:ENABLES_PER_ELEMENT-1] Element_enables[0:NUM_ELEMS-1];


  //--------------------------------------------------------------------------------
  // Functions & tasks
  //--------------------------------------------------------------------------------

  function automatic Vector_element modulo_extract(Vector_double_element x,
      Valu_type conf);
    Vector_element rv;

    unique case(conf)
      VALU_TYPE_FULL: rv = x[ELEM_SIZE-1:0];
      VALU_TYPE_HALF: rv = {
        x[ELEM_SIZE+(ELEM_SIZE/2)-1 -: ELEM_SIZE/2],
        x[ELEM_SIZE/2-1 -: ELEM_SIZE/2]
      };
      VALU_TYPE_QUARTER: rv = {
        x[ELEM_SIZE+(ELEM_SIZE/2)+(ELEM_SIZE/4)-1 -: ELEM_SIZE/4],
        x[ELEM_SIZE+(ELEM_SIZE/2)-(ELEM_SIZE/4)-1 -: ELEM_SIZE/4],
        x[          (ELEM_SIZE/2)+(ELEM_SIZE/4)-1 -: ELEM_SIZE/4],
        x[          (ELEM_SIZE/2)-(ELEM_SIZE/4)-1 -: ELEM_SIZE/4]
      };
      default: begin
        rv = 'x;
      end
    endcase

    return rv;
  endfunction


  function automatic Vector_element saturating_fractional_extract(Vector_double_element x,
      Valu_type conf);
    Vector_element rv;

    unique case(conf)
      VALU_TYPE_FULL: begin
        rv = x[2*ELEM_SIZE-1:ELEM_SIZE];
      end

      VALU_TYPE_HALF: begin
        rv[ELEM_SIZE-1   : ELEM_SIZE/2] = x[2*ELEM_SIZE-1 -: ELEM_SIZE/2];
        rv[ELEM_SIZE/2-1 : 0          ] = x[ELEM_SIZE-1   -: ELEM_SIZE/2];
      end

      default: begin
        rv = 'x;
      end
    endcase

    return rv;
  endfunction


  /** Do sign extension depending on the vector configuration */
  function automatic Vector_double_element sign_extend(Vector_element x, Valu_type conf);
    Vector_double_element rv;
    Vector_element_halfs halfs;
    Vector_element_quarters quarters;

    halfs = Vector_element_halfs'(x);
    quarters = Vector_element_quarters'(x);

    unique case(conf)
      VALU_TYPE_FULL: rv = { {ELEM_SIZE{x[$left(x)]}}, x };
      VALU_TYPE_HALF: rv = {
        {$bits(Vector_half_element){halfs[0][$left(Vector_half_element)]}},
        halfs[0],
        {$bits(Vector_half_element){halfs[1][$left(Vector_half_element)]}},
        halfs[1]
      };
      VALU_TYPE_QUARTER: rv = {
        {$bits(Vector_quarter_element){quarters[0][$left(Vector_quarter_element)]}},
        quarters[0],
        {$bits(Vector_quarter_element){quarters[1][$left(Vector_quarter_element)]}},
        quarters[1],
        {$bits(Vector_quarter_element){quarters[2][$left(Vector_quarter_element)]}},
        quarters[2],
        {$bits(Vector_quarter_element){quarters[3][$left(Vector_quarter_element)]}},
        quarters[3]
      };
      default: rv = 'x;
    endcase

    return rv;
  endfunction


  function automatic Vector_double_element mask_conditional(Vector_double_element result,
      Vector_double_element original,
      logic[0:ENABLES_PER_ELEMENT-1] mask);
    Vector_double_element bit_mask;

    for(int i=0; i<ENABLES_PER_ELEMENT; i++)
      if( mask[i] )
        bit_mask[$left(bit_mask) - i*2*(ELEM_SIZE/ENABLES_PER_ELEMENT) -: 2*(ELEM_SIZE/ENABLES_PER_ELEMENT)] = '1;
      else
        bit_mask[$left(bit_mask) - i*2*(ELEM_SIZE/ENABLES_PER_ELEMENT) -: 2*(ELEM_SIZE/ENABLES_PER_ELEMENT)] = '0;

    return (result & bit_mask) | (original & ~bit_mask);
  endfunction


  function automatic Vector_double_element shift_left_saturating(Vector_double_element x,
      Valu_type conf);
    Vector_double_element rv;

    unique case(conf)
      VALU_TYPE_FULL:  begin
        if( (x[$left(x) -: 2] == 2'b01) )
          rv = { 1'b0, {2*ELEM_SIZE-1{1'b1}} };
        else
          rv = { x[$left(x)-1:$right(x)], 1'b0 };
      end

      VALU_TYPE_HALF: begin
        if( (x[2*ELEM_SIZE-1 -: 2] == 2'b01) )
          rv[2*ELEM_SIZE-1 -: ELEM_SIZE] = { 1'b0, {ELEM_SIZE-1{1'b1}} };
        else
          rv[2*ELEM_SIZE-1 -: ELEM_SIZE] = { x[2*ELEM_SIZE-2 : ELEM_SIZE], 1'b0 };

        if( (x[ELEM_SIZE-1 -: 2] == 2'b01) )
          rv[ELEM_SIZE-1 -: ELEM_SIZE] = { 1'b0, {ELEM_SIZE-1{1'b1}} };
        else
          rv[ELEM_SIZE-1 -: ELEM_SIZE] = { x[ELEM_SIZE-2 : 0], 1'b0 };
      end

      default: rv = 'x;
    endcase

    return rv;
  endfunction


  function automatic Vector_double_element shift_element_left_saturating(Vector_double_element x,
      Valu_type conf);
    Vector_double_element rv;

    if( conf == VALU_TYPE_FULL ) begin
      unique case(x[ELEM_SIZE -: 2])
        2'b10:       rv = { 1'b1, {2*ELEM_SIZE-1{1'b0}} };
        2'b01:       rv = { 1'b0, {2*ELEM_SIZE-1{1'b1}} };
        default:     rv = { x[ELEM_SIZE-1 : 0], {ELEM_SIZE{1'b0}} };
      endcase
    end else if( conf == VALU_TYPE_HALF ) begin
      unique case(x[ELEM_SIZE/2 -: 2])
        2'b10:       rv[ELEM_SIZE-1 : 0] = { 1'b1, {ELEM_SIZE-1{1'b0}} };
        2'b01:       rv[ELEM_SIZE-1 : 0] = { 1'b0, {ELEM_SIZE-1{1'b1}} };
        default:     rv[ELEM_SIZE-1 : 0] = { x[ELEM_SIZE/2 - 1 : 0], {ELEM_SIZE/2{1'b0}} };
      endcase

      unique case(x[2*ELEM_SIZE - ELEM_SIZE/2 -: 2])
        2'b10:       rv[2*ELEM_SIZE-1 : ELEM_SIZE] = { 1'b1, {ELEM_SIZE-1{1'b0}} };
        2'b01:       rv[2*ELEM_SIZE-1 : ELEM_SIZE] = { 1'b0, {ELEM_SIZE-1{1'b1}} };
        default:     rv[2*ELEM_SIZE-1 : ELEM_SIZE] = { x[2*ELEM_SIZE - ELEM_SIZE/2 - 1 : ELEM_SIZE], {ELEM_SIZE/2{1'b0}} };
      endcase
    end else begin
      rv = 'x;
    end

    return rv;
  endfunction



  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------

  // data signals
  Vector_elems va, vb, vy;
  Double_vector_elems accumulator;


  //--------------------------------------------------------------------------------
  // Datapath
  //--------------------------------------------------------------------------------
  
  generate 
    genvar i_elem;
    for(i_elem=0; i_elem<NUM_ELEMS; i_elem++) begin : gen_elem
      Vector_double_element a_ext;
      Vector_double_element b_ext;
      Vector_double_element next_product;
      Vector_double_element next_sum;
      Vector_double_element result, next_result;
      Vector_double_element add_in_b_ext;
      Vector_double_element next_add_res, add_res;
      Vector_double_element add_res_sat;
      logic[0:ENABLES_PER_ELEMENT-1] mult_en;
      logic[0:ENABLES_PER_ELEMENT-1] mult_en_shr[1:MULT_STAGES-1];
      logic[0:ENABLES_PER_ELEMENT-1] add_en;
      logic[0:ENABLES_PER_ELEMENT-1] add_en_shr[1:ADD_STAGES-1];
      logic[MULT_STAGES-1:0] mult_pipe_enable;
      logic[ADD_STAGES-1:0] add_pipe_enable;
      logic[0:1] neg_ops;
      logic[0:1] acc_a_msb, acc_b_msb;

      // input
      always_comb
        unique case({ctrl.mult_by_one, ctrl.mult_conf})
          {1'b1, VALU_TYPE_FULL}:  vb[i_elem] = { {ELEM_SIZE-1{1'b0}}, 1'b1 };
          {1'b1, VALU_TYPE_HALF}:  vb[i_elem] = { {ELEM_SIZE/2-1{1'b0}}, 1'b1, {ELEM_SIZE/2-1{1'b0}}, 1'b1 };
          {1'b0, VALU_TYPE_FULL},
          {1'b0, VALU_TYPE_HALF}:  vb[i_elem] = b[(NUM_ELEMS-i_elem) * ELEM_SIZE -1 -: ELEM_SIZE];
          default:                 vb[i_elem] = 'x;
        endcase


      assign va[i_elem] = a[(NUM_ELEMS-i_elem) * ELEM_SIZE -1 -: ELEM_SIZE];

      always_comb begin
        unique case(ctrl.cond)
          Pu_inst::Fxv_cond_null: mult_en = '1;
          Pu_inst::Fxv_cond_gt:   mult_en = vcr[i_elem].gt;
          Pu_inst::Fxv_cond_lt:   mult_en = vcr[i_elem].lt;
          Pu_inst::Fxv_cond_eq:   mult_en = vcr[i_elem].eq;
          default:                mult_en = 'x;
        endcase
      end



      //--------------------------------------------------------------------------------
      // mutliplier or adder
      //--------------------------------------------------------------------------------

      Valu_simd_mult_add #(
        .width(ELEM_SIZE),
        .no_confs(NUM_SUB_ELEMENT_CONFIGS),
        .num_stages(MULT_STAGES)
      ) mult_add (
        .clk,
        .enable(ctrl.mult_pipe_enable[0]),
        .negate_b(ctrl.negate_b),
        .mult_shift(ctrl.mult_shift),
        .shift_fractional(ctrl.shift_fractional),
        .result_sel(ctrl.result_sel),
        .a(va[i_elem]),
        .b(vb[i_elem]),
        .conf(ctrl.mult_conf),
        .result(result)
      );

      always_ff @(posedge clk) begin
        if( !ctrl.stall ) begin
          mult_en_shr[1] <= mult_en;
          for(int i=2; i<MULT_STAGES; i++)
            mult_en_shr[i] <= mult_en_shr[i-1];
        end
      end

      //--------------------------------------------------------------------------------
      // adder
      //--------------------------------------------------------------------------------

      // adder input selection
      always_comb begin
        // default assignment
        add_in_b_ext = accumulator[i_elem];

        if( ctrl.add_to_zero )
          add_in_b_ext = '0;
      end


      Valu_simd_add #(
        .width(2*ELEM_SIZE),
        .no_confs(NUM_SUB_ELEMENT_CONFIGS)
      ) acc (
        .a(result),
        .b(add_in_b_ext),
        .res(next_add_res),
        .conf(ctrl.add_conf)
      );


      always_comb begin
        add_pipe_enable[0] = (| add_en) & ctrl.add_pipe_enable[0];

        for(int i=0; i<ADD_STAGES; i++) begin
          add_pipe_enable[i] = (| add_en_shr[i]) & ctrl.add_pipe_enable[i];
        end
      end

      assign add_en = mult_en_shr[MULT_STAGES-1];

      always_ff @(posedge clk) begin
        if( !ctrl.stall ) begin
          add_en_shr[0] <= add_en;

          for(int i=1; i<ADD_STAGES; i++)
            add_en_shr[i] <= add_en_shr[i-1];
        end
      end

      DW_pl_reg #(
        //.width($bits(next_add_res) + $bits(acc_a_msb) + $bits(acc_b_msb)),
        .width(2*ELEM_SIZE + 2 + 2),
        .in_reg(0),
        .out_reg(0),
        .stages(ADD_STAGES+1),
        .rst_mode(0) // asynchronous reset
      ) add_out_pipe (
        .clk,
        //.rst_n(~reset),
        .rst_n(1'b1),
        .enable(add_pipe_enable),
        //.enable({ADD_STAGES{(| add_pipe_enale)}}),
        .data_in({
          next_add_res,
          result[$left(result)],
          result[ELEM_SIZE-1],
          add_in_b_ext[$left(add_in_b_ext)],
          add_in_b_ext[ELEM_SIZE-1]
        }),
        .data_out({
          add_res,
          acc_a_msb,
          acc_b_msb
        })
      );


      always_comb begin : saturate_accumulator
        if( ctrl.round_conf == VALU_TYPE_FULL ) begin
          logic cout;
          logic cin;

          // explicitly compute carry-out and carry-in of highest bit in accumulator sum
          cout = (acc_a_msb[0] & acc_b_msb[0])
              | ((add_res[$left(add_res)] ^ acc_a_msb[0] ^ acc_b_msb[0])
                & (acc_a_msb[0] | acc_b_msb[0]));
          cin = add_res[$left(add_res)] ^ acc_a_msb[0] ^ acc_b_msb[0];

          // if carry-in and carry-out on the highest bit are not identical, there is an overflow
          if( {cout, cin} == 2'b10 )
            add_res_sat = {1'b1, {ELEM_SIZE*2-1{1'b0}}};
          else if( {cout, cin} == 2'b01 )
            add_res_sat = {1'b0, {ELEM_SIZE*2-1{1'b1}}};
          else
            add_res_sat = add_res;
        end else if( ctrl.round_conf == VALU_TYPE_HALF ) begin
          for(int i=0; i<2; i++) begin
            logic cout;
            logic cin;

            // explicitly compute carry-out and carry-in of highest bit in accumulator sum
            cout = (acc_a_msb[i] & acc_b_msb[i])
                | ((add_res[(2-i)*ELEM_SIZE-1] ^ acc_a_msb[i] ^ acc_b_msb[i])
                  & (acc_a_msb[i] | acc_b_msb[i]));
            cin = add_res[(2-i)*ELEM_SIZE-1] ^ acc_a_msb[i] ^ acc_b_msb[i];

            // if carry-in and carry-out on the highest bit are not identical, there is an overflow
            if( {cout, cin} == 2'b10 )
              add_res_sat[(2-i)*ELEM_SIZE-1 -: ELEM_SIZE] = {1'b1, {ELEM_SIZE-1{1'b0}}};
            else if( {cout, cin} == 2'b01 )
              add_res_sat[(2-i)*ELEM_SIZE-1 -: ELEM_SIZE] = {1'b0, {ELEM_SIZE-1{1'b1}}};
            else
              add_res_sat[(2-i)*ELEM_SIZE-1 -: ELEM_SIZE] = add_res[(2-i)*ELEM_SIZE-1 -: ELEM_SIZE];
          end
        end else begin
          add_res_sat = 'x;
        end
      end


      always_ff @(posedge clk or posedge reset)
        if( reset )
          accumulator[i_elem] <= '0;
        else begin
          if( ctrl.save_to_accum ) begin
            if( ctrl.saturate )
              accumulator[i_elem] <= mask_conditional(add_res_sat,
                  accumulator[i_elem], 
                  write_mask[i_elem]);
            else
              accumulator[i_elem] <= mask_conditional(add_res,
                  accumulator[i_elem], 
                  write_mask[i_elem]);
          end
        end


      always_comb begin
        unique casez(ctrl.saturate)
          1'b0: vy[i_elem] = modulo_extract(add_res, ctrl.round_conf);
          1'b1: vy[i_elem] = saturating_fractional_extract(add_res_sat, ctrl.round_conf);

          default:
            vy[i_elem] = 'x;
        endcase
      end


      always_ff @(posedge clk) begin
        if( !ctrl.stall ) 
          write_mask[i_elem] <= add_en_shr[ADD_STAGES-1];
      end


      //--------------------------------------------------------------------------------
      // Assertions
      //--------------------------------------------------------------------------------

`ifndef SYNTHESIS

      /**
       * Accumulating in full mode saturates the accumulation register.
       */
      property full_accumulator_is_saturating;
        longint a, b;

        @(posedge clk) disable iff(reset)
        ( (add_pipe_enable[0] && (ctrl.add_conf == VALU_TYPE_FULL),
            a = signed'(result),
            b = signed'(add_in_b_ext))
          |-> ##ADD_STAGES  !ctrl.saturate 
            || ( 
              (!(a + b > 2 ** (2*ELEM_SIZE-1) - 1) || (add_res_sat == 2 ** (2*ELEM_SIZE-1)-1))
              && (!(a + b < -2 ** (2*ELEM_SIZE-1)) || (add_res_sat == -2 ** (2*ELEM_SIZE-1)))
            )
        );
      endproperty

      check_full_accumulator_is_saturating: assert property( full_accumulator_is_saturating );
      cover_full_accumulator_is_saturating: cover property( full_accumulator_is_saturating );


      /**
       * Input operands are not undefined.
       */
      property defined_operands;
        @(posedge clk) disable iff(reset)
        ( mult_pipe_enable[0] 
          |-> (!$isunknown(va[i_elem]) && !$isunknown(vb[i_elem])) );
      endproperty

      check_defined_operands: assert property( defined_operands );
      cover_defined_operands: cover property( defined_operands );

`endif  /* SYNTHESIS */



    end : gen_elem

    always_comb begin
      for(int i=0; i<NUM_ELEMS; i++) begin
        y[(NUM_ELEMS-i)*ELEM_SIZE-1 -: ELEM_SIZE] = vy[i];
      end
    end

  endgenerate



`ifndef SYNTHESIS

  //--------------------------------------------------------------------------------
  // Assertions
  //--------------------------------------------------------------------------------
  
  initial begin
    check_vector_multiple_of_scalar: assert((NUM_ELEMS * ELEM_SIZE) % SCALAR_SIZE == 0) else
      $fatal("The vector size must be an integer multiple of the scalar size.");

    check_num_configs: assert(NUM_SUB_ELEMENT_CONFIGS <= 3) else 
      $warning("Only three configurations are supported by Valu_pkg::Valu_type at the moment!");

    check_mult_pipe_stages: assert(MULT_STAGES > 0) else
      $fatal("The multiplier pipeline must be at least one stage long");

    check_add_pipe_stages: assert(ADD_STAGES > 0) else
      $fatal("The adder pipeline must be at least one stage long");
  end


  //--------------------------------------------------------------------------------
  // Coverage
  //--------------------------------------------------------------------------------
  
  // TODO include other configurations in coverage
  covergroup cg_operands(int i) @(posedge clk);
    option.per_instance = 1;

    va: coverpoint va[i] iff(!reset && ctrl.mult_pipe_enable[0]) {
      bins zero = { 0 };
      bins full_max = { {ELEM_SIZE-1{1'b1}} };
      bins full_neg_max = { {1'b1, {ELEM_SIZE-1{1'b0}}} };
      bins full_pos_max = { {1'b0, {ELEM_SIZE-1{1'b1}}} };
      bins full_pos = { [ 1 : 2**(ELEM_SIZE-1) - 1 ] };
      bins full_neg = { [ 2**(ELEM_SIZE-1) : 2**ELEM_SIZE - 1 ] };
      //bins others[] = default;
    }

    vb: coverpoint vb[i] iff(!reset && ctrl.mult_pipe_enable[0]) {
      bins zero = { 0 };
      bins full_max = { {ELEM_SIZE-1{1'b1}} };
      bins full_neg_max = { {1'b1, {ELEM_SIZE-1{1'b0}}} };
      bins full_pos_max = { {1'b0, {ELEM_SIZE-1{1'b1}}} };
      bins full_pos = { [ 1 : 2**(ELEM_SIZE-1) - 1 ] };
      bins full_neg = { [ 2**(ELEM_SIZE-1) : 2**ELEM_SIZE - 1 ] };
      //bins others[] = default;
    }

    vcr: coverpoint vcr[i] iff(!reset && ctrl.mult_pipe_enable[0]) {
      bins full[] = { 24'hf00, 24'h0f0, 24'h00f };
    }

    mult_by_one: coverpoint ctrl.mult_by_one iff(!reset && ctrl.mult_pipe_enable[0]);
    mult_shift: coverpoint ctrl.mult_shift iff(!reset && ctrl.mult_pipe_enable[0]);
    negate_b: coverpoint ctrl.negate_b iff(!reset && ctrl.mult_pipe_enable[0]);
    cond: coverpoint ctrl.cond iff(!reset && ctrl.mult_pipe_enable[0]);
    result_sel: coverpoint ctrl.result_sel iff(!reset && ctrl.mult_pipe_enable[0]);
    shift_fractional: coverpoint ctrl.shift_fractional iff(!reset && ctrl.mult_pipe_enable[0]);

    c1: cross va, vb, vcr, mult_by_one, mult_shift, cond { option.weight = 10; }
    c2: cross va, vb, vcr, cond, result_sel { option.weight = 10; }
    c3: cross va, vb, vcr, cond, shift_fractional { option.weight = 10; }
    operand_combinations: cross va, vb, vcr { option.weight = 10; }
  endgroup

  generate
    genvar cov_i_elem;
    for(cov_i_elem=0; cov_i_elem<NUM_ELEMS; cov_i_elem++) begin : gen_cov_elem
      cg_operands cg_operands_inst = new(cov_i_elem);
    end : gen_cov_elem
  endgenerate

  

`endif  /* SYNTHESIS */

endmodule




/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
