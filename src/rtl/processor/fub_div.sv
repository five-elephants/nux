/** _use_m4_ macros
* include(ops.m4)
* */

// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Fub_div
  ( input logic clk, reset,

    input Frontend::Issue_slot inst,
    Operand_if.read opbus,

    output Backend::Result_bus resbus );

import Backend::*;
import Pu_inst::*;
import Pu_types::*;

//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

Inst ir;
Frontend::Thread_id thread_d;

logic div_en;
logic next_div_en;

logic div_unsigned;
logic next_div_unsigned;

logic div_ready;
logic div_complete;

Word     div_res;
Cr_field div_crf;

Word aa, bb;
logic oe_d;
logic so;
logic so_d;
logic inst_valid_d;

assign ir = inst.ir;

always_comb aa = opbus.opbus_0.a;
always_comb bb = opbus.opbus_0.b;
assign so = opbus.opbus_0.so;

//---------------------------------------------------------------------------
// Decode logic
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
always_comb  begin
  logic[14:0] cop;

  next_div_unsigned = 1'b0;

  cop = {ir.xo.opcd, ir.xo.xo};
  case(cop)
    {Op_alu_xo, Xop_divwu}: begin
      next_div_unsigned = 1'b1;
    end
  endcase
end

always_comb begin
  OPCMP(ir)
    DIV_OPS:
      next_div_en = 1'b1;

    default:
      next_div_en = 1'b0;
  ENDOPCMP
end

always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    div_en <= 1'b0;
    div_unsigned <= 1'b0;

    thread_d <= '0;
    oe_d <= 1'b0;
  end else begin
    div_en <= next_div_en;

    if( inst.valid ) begin
      div_unsigned <= next_div_unsigned;
      
      thread_d <= inst.thread;

      oe_d <= inst.ir.xo.oe;
    end
  end

always_ff @(posedge clk or posedge reset)
  if( reset )
    inst_valid_d <= 1'b0;
  else
    inst_valid_d <= inst.valid;

always_ff @(posedge clk)
  if( inst_valid_d )
    so_d <= so;
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Execution logic
//---------------------------------------------------------------------------

Div_dw_seq div
  (	.clk(clk),
    .reset(reset),
    .en(div_en),
    .uns(div_unsigned),

    .a(aa),
    .b(bb),
    .crf(div_crf),

    .ready(div_ready),
    .complete(div_complete),
    .quotient(div_res),
    .remainder(),
    .div_by_zero() );


//---------------------------------------------------------------------------
// Output stage
//---------------------------------------------------------------------------

assign resbus.valid = 1'b1;

always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    resbus.res_a <= '0;
    resbus.crf <= '0;
    resbus.ov <= 1'b0;
    resbus.cout <= 1'b0;
    resbus.res_b <= '0;
    resbus.msr <= '0;
  end else begin
    // default assignment
    resbus.res_a <= '0;
    resbus.crf <= '0;
    resbus.ov <= 1'b0;
    resbus.cout <= 1'b0;
    resbus.res_b <= '0;
    resbus.msr <= '0;

    if( div_complete )
    begin
      resbus.cout <= 1'b0;
      resbus.res_b <= '0;
      resbus.msr <= '0;
      resbus.res_a <= div_res;
      resbus.crf <= div_crf;
      resbus.crf.ov <= so_d | (div_crf.ov & oe_d);
      resbus.ov <= div_crf.ov;
    end
  end

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
