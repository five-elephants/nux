// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_cmp_ctrl
  #(parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16)
  ( input logic clk, reset,
    input logic valid,
    input Pu_inst::Fxv_opcd xo,
    input Pu_types::Word g,
    output logic result_avail,
    output logic write_vcr,
    Vector_cmp_ctrl_if.ctrl ctrl,
    output logic ready );

  always_comb begin
    // default assignments
    ready = 1'b1;
    ctrl.elem_type = Valu_pkg::VALU_TYPE_FULL;

    if( valid ) begin
      unique case(xo)
        Pu_inst::Xop_fxvcmph: begin
          ctrl.elem_type = Valu_pkg::VALU_TYPE_FULL;
        end

        Pu_inst::Xop_fxvcmpb: begin
          ctrl.elem_type = Valu_pkg::VALU_TYPE_HALF;
        end

        default: begin
          ctrl.elem_type = Valu_pkg::VALU_TYPE_UNDEF;
        end
      endcase
    end
  end


  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      result_avail <= 1'b0;
      write_vcr <= 1'b0;
    end else begin
      result_avail <= valid;
      write_vcr <= valid;
    end

endmodule


/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
