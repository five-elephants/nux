// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_permute_ctrl
  #(parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16)
  ( input logic clk, reset,
    input logic valid,
    input Pu_inst::Fxv_opcd xo,
    output logic result_avail,
    input logic stall,
    Vector_permute_ctrl_if.ctrl ctrl,
    output logic ready,
    input Pu_types::Word g,
    input Vector::Permute_size size,
    input logic[4:0] shift );

  Vector::Permute_op next_op;

  logic next_valid_d, valid_d;
  logic next_pack_upper;
  logic next_pack_lower;
  logic next_unpack_left;
  logic next_unpack_right;
  Pu_types::Word next_g;
  Vector::Permute_size next_size;
  logic[4:0] next_shift;
  logic next_ready;
  logic next_result_avail;


  always_comb begin
    // default assignments
    next_op = Vector::PERMUTE_PACK;
    next_valid_d = valid;
    next_result_avail = valid_d;
    next_g = g;
    next_size = size;
    next_shift = shift;
    next_pack_upper = 1'b0;
    next_pack_lower = 1'b0;
    next_unpack_left = 1'b0;
    next_unpack_right = 1'b0;

    unique case(xo)
      Pu_inst::Xop_fxvpckbu:
        next_pack_upper = 1'b1;

      Pu_inst::Xop_fxvpckbl:
        next_pack_lower = 1'b1;

      Pu_inst::Xop_fxvupckbl:
        next_unpack_left = 1'b1;

      Pu_inst::Xop_fxvupckbr:
        next_unpack_right = 1'b1;

      Pu_inst::Xop_fxvsplath: begin
        next_op = Vector::PERMUTE_SPLAT;
      end

      Pu_inst::Xop_fxvsplatb: begin
        next_op = Vector::PERMUTE_SPLATB;
      end

      Pu_inst::Xop_fxvshh: begin
        next_op = Vector::PERMUTE_SHIFT;
      end

      Pu_inst::Xop_fxvshb: begin
        next_op = Vector::PERMUTE_SHIFTB;
      end

      Pu_inst::Xop_fxvsel: begin
        next_op = Vector::PERMUTE_SELECT;
      end

      default: begin
      end
    endcase
  end

  assign ready = 1'b1;
  assign ctrl.keep_res = ~stall;

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      valid_d <= 1'b0;
      ctrl.op <= Vector::PERMUTE_PACK;
      ctrl.pack_lower <= 1'b0;
      ctrl.pack_upper <= 1'b0;
      ctrl.unpack_left <= 1'b0;
      ctrl.unpack_right <= 1'b0;
      ctrl.g <= '0;
      ctrl.size <= '0;
      ctrl.shift <= '0;
      result_avail <= 1'b0;
    end else begin
      if( !stall ) begin
        valid_d <= next_valid_d;
        ctrl.op <= next_op;
        ctrl.pack_lower <= next_pack_lower;
        ctrl.pack_upper <= next_pack_upper;
        ctrl.unpack_left <= next_unpack_left;
        ctrl.unpack_right <= next_unpack_right;
        ctrl.g <= next_g;
        ctrl.size <= next_size;
        ctrl.shift <= next_shift;
        result_avail <= next_result_avail;
      end
    end


`ifndef SYNTHESIS

  // valid may not be active while stall is active
  property no_valid_while_stalled;
    logic valid_state;

    @(posedge clk) disable iff(reset)
    ( (stall,valid_state = valid) |=> (valid == valid_state) );
  endproperty

  check_no_valid_while_stalled: assert property(no_valid_while_stalled);
  cover_no_valid_while_stalled: cover property(no_valid_while_stalled);

`endif  /* SYNTHESIS */

endmodule


/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
