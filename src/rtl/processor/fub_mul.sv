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


module Fub_mul
  #(parameter bit REGISTER_RESBUS = 1'b0)
  ( input logic clk, reset,

    input Frontend::Issue_slot inst,
    Operand_if.read opbus,

    output Backend::Result_bus resbus );

import Backend::*;
import Pu_inst::*;
import Pu_types::*;


localparam bit REGISTER_MUL_OUT = 1'b0;
localparam bit REGISTER_MUL_RES = 1'b0;
localparam int CTRL_LATENCY_A = Frontend::mul_latency -1;
localparam int CTRL_LATENCY_B = Frontend::mul_latency;

//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

Inst ir;
Frontend::Thread_id thread_d;

logic mul_en;
logic next_mul_en;

logic mul_high;
//logic mul_high_d[0:Frontend::mul_latency-3];
logic mul_high_d;
logic so;
//logic so_d[0:Frontend::mul_latency-3];  // so is first available after operand fetch
//logic oe_d[0:Frontend::mul_latency-2];  // oe is directly available after issue
logic so_d;
logic oe_d;
logic mul_unsigned;
logic next_mul_high;
logic next_mul_unsigned;
logic next_div_unsigned;

Word     mul_res_hi, mul_res_lo;
Cr_field mul_crf_hi, mul_crf_lo;

Word aa, bb;

assign ir = inst.ir;

assign aa = opbus.opbus_0.a;
assign bb = opbus.opbus_0.b;
assign so = opbus.opbus_0.so;

//---------------------------------------------------------------------------
// Decode logic
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
always_comb  begin
  logic[14:0] cop;

  next_mul_high = 1'b0;
  next_mul_unsigned = 1'b0;

  cop = {ir.xo.opcd, ir.xo.xo};
  case(cop)
    {Op_alu_xo, Xop_mulhwu}: begin
      next_mul_high = 1'b1;
      next_mul_unsigned = 1'b1;
    end

    {Op_alu_xo, Xop_mulhw}: begin
      next_mul_high = 1'b1;
    end
  endcase
end

always_comb begin
  OPCMP(ir)
    MUL_OPS:
      next_mul_en = 1'b1;

    default:
      next_mul_en = 1'b0;
  ENDOPCMP
end

always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    mul_en <= 1'b0;
    mul_high <= 1'b0;
    mul_unsigned <= 1'b0;

    thread_d <= '0;
  end else begin
    mul_en <= next_mul_en;

    if( inst.valid ) begin
      mul_high <= next_mul_high;
      mul_unsigned <= next_mul_unsigned;
      
      thread_d <= inst.thread;
    end
  end


Shift_reg #(CTRL_LATENCY_A) shift_mul_high (
  .clk,
  .reset,
  .en(1'b1),
  .in(mul_high),
  .out(mul_high_d)
);

Shift_reg #(CTRL_LATENCY_A) shift_so (
  .clk,
  .reset,
  .en(1'b1),
  .in(so),
  .out(so_d)
);

Shift_reg #(CTRL_LATENCY_B) shift_oe (
  .clk,
  .reset,
  .en(1'b1),
  .in(inst.ir.xo.oe),
  .out(oe_d)
);

//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Execution logic
//---------------------------------------------------------------------------

// using DesignWare multiplier
Mul_pipe #(
    .REGISTER_MUL_OUT(REGISTER_MUL_OUT),
    .REGISTER_RESULT(REGISTER_MUL_RES) 
  ) mul ( 
    .clk(clk),
    .reset(reset),
    .en(mul_en),
    .uns(mul_unsigned),

    .a(aa),
    .b(bb),
    
    .ready(),
    .complete(),
    .res_hi(mul_res_hi),
    .res_lo(mul_res_lo),
    .crf_hi(mul_crf_hi),
    .crf_lo(mul_crf_lo) );

//---------------------------------------------------------------------------
// Output stage
//---------------------------------------------------------------------------

assign resbus.valid = 1'b1;

generate if( REGISTER_RESBUS == 1'b1 ) begin : gen_high_latency
  //always_ff @(posedge clk)
  //begin
    //mul_high_d[0] <= mul_high;
    //for(int i=1; i<=$right(mul_high_d); i++)
      //mul_high_d[i] <= mul_high_d[i-1];
  //end

  //always_ff @(posedge clk)
  //begin
    //so_d[0] <= so;
    //for(int i=1; i<=$right(so_d); i++)
      //so_d[i] <= so_d[i-1];
  //end

  //always_ff @(posedge clk)
  //begin
    //oe_d[0] <= inst.ir.xo.oe;
    //for(int i=1; i<=$right(oe_d); i++)
      //oe_d[i] <= oe_d[i-1];
  //end

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      resbus.res_a <= '0;
      resbus.crf <= '0;
      resbus.ov <= 1'b0;
      resbus.cout <= 1'b0;
      resbus.res_b <= '0;
      resbus.msr <= '0;
    end else begin
      resbus.cout <= 1'b0;
      resbus.res_b <= '0;
      resbus.msr <= '0;

      if( mul_high_d ) begin
        resbus.res_a <= mul_res_hi;
        resbus.crf <= mul_crf_hi;
        resbus.crf.ov <= so_d;
        resbus.ov <= 1'b0;
      end else begin
        resbus.res_a <= mul_res_lo;
        resbus.crf <= mul_crf_lo;

        // CR.OV is set to the previous value of XER.SO. If OE=1, XER.SO will
        // be set by this instruction and thus also CR.OV.
        resbus.crf.ov <= so_d | (mul_crf_lo.ov & oe_d);
        resbus.ov <= mul_crf_lo.ov;
      end
    end
end else begin : gen_low_latency
  //assign
    //mul_high_d[$right(mul_high_d)] = mul_high,
    //so_d[$right(so_d)] = so;

  //always_ff @(posedge clk)
    //oe_d[$right(oe_d)] <= inst.ir.xo.oe;

  always_comb begin
    resbus.cout = 1'b0;
    resbus.res_b = '0;
    resbus.msr = '0;

    if( mul_high_d ) begin
      resbus.res_a = mul_res_hi;
      resbus.crf = mul_crf_hi;
      resbus.crf.ov = so_d;
      resbus.ov = 1'b0;
    end else begin
      resbus.res_a = mul_res_lo;
      resbus.crf = mul_crf_lo;

      // CR.OV is set to the previous value of XER.SO. If OE=1, XER.SO will
      // be set by this instruction and thus also CR.OV.
      resbus.crf.ov = so_d | (mul_crf_lo.ov & oe_d);
      resbus.ov = mul_crf_lo.ov;
    end
  end
end
endgenerate

endmodule

