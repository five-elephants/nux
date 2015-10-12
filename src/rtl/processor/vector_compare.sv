// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_compare
  #(parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16)
  ( input logic clk, reset,
    Vector_cmp_ctrl_if.cmp ctrl,
    input logic[NUM_ELEMS*ELEM_SIZE - 1 : 0] a,
    output Vector::Compare[0:NUM_ELEMS-1] vcr );

  import Vector::*;

  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------

  typedef logic signed[ELEM_SIZE-1:0] Vector_element;
  typedef logic signed[ELEM_SIZE/2-1:0] Vector_half_element;
  typedef logic signed[ELEM_SIZE/4-1:0] Vector_quarter_element;
  typedef Vector_element Vector[0:NUM_ELEMS-1];
  typedef Vector_half_element[0:1] Vector_in_halfs[0:NUM_ELEMS-1];
  typedef Vector_quarter_element[0:3] Vector_in_quarters;
  typedef logic[NUM_ELEMS*ELEM_SIZE-1:0] Vector_raw;

  Vector u;
  Vector_in_halfs v;
  //Vector_in_quarters x;

  always_comb begin
    {>>{ u }} = a;
    {>>{ v }} = a;
    //{>>{ x }} = a;
  end

  generate
    genvar elem_i;
    for(elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin : gen_elem

      Compare next_vcr_elem;

      always_comb 
        unique case(ctrl.elem_type)
          Valu_pkg::VALU_TYPE_FULL: begin
            next_vcr_elem.eq = {$bits(vcr[elem_i].eq){ u[elem_i] == 0 }};
            next_vcr_elem.gt = {$bits(vcr[elem_i].gt){ (u[elem_i][ELEM_SIZE-1] == 0) & !(u[elem_i] == 0) }};
            next_vcr_elem.lt = {$bits(vcr[elem_i].lt){ u[elem_i][ELEM_SIZE-1] == 1 }};
          end

          Valu_pkg::VALU_TYPE_HALF: begin
            next_vcr_elem.eq = {
              {$bits(vcr[elem_i].eq)/2{ v[elem_i][0] == 0 }},
              {$bits(vcr[elem_i].eq)/2{ v[elem_i][1] == 0 }}
            };
            next_vcr_elem.gt = {
              {$bits(vcr[elem_i].gt)/2{ (v[elem_i][0][ELEM_SIZE/2-1] == 0) & !(v[elem_i][0] == 0) }},
              {$bits(vcr[elem_i].gt)/2{ (v[elem_i][1][ELEM_SIZE/2-1] == 0) & !(v[elem_i][1] == 0) }}
            };
            next_vcr_elem.lt = {
              {$bits(vcr[elem_i].lt)/2{ v[elem_i][0][ELEM_SIZE/2-1] == 1 }},
              {$bits(vcr[elem_i].lt)/2{ v[elem_i][1][ELEM_SIZE/2-1] == 1 }}
            };
            //$display("next_vcr_elem = (%h, %h, %h), v[0] = %h, v[1] = %h",
              //next_vcr_elem.eq, next_vcr_elem.gt, next_vcr_elem.lt,
              //v[0], v[1]);
          end

          default: begin
            next_vcr_elem.eq = 1'bx;
            next_vcr_elem.gt = 1'bx;
            next_vcr_elem.lt = 1'bx;
          end
        endcase

      always_ff @(posedge clk) begin
        vcr[elem_i] <= next_vcr_elem;
      end

    end : gen_elem
  endgenerate



endmodule


/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
