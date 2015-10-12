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


module Fub_io
  ( input logic clk, reset,
    input Frontend::Issue_slot inst,
    Operand_if.read opbus,
    output Backend::Result_bus resbus,
    output logic pipe_empty,

    Bus_if.master iobus,

    Delayed_wb_if.fub dwb);

import Pu_inst::*;
import Pu_types::*;
import Backend::*;

//---------------------------------------------------------------------------
// Local types & signals
//---------------------------------------------------------------------------

Inst ir;
Word aa, bb, cc;
logic en, next_en;
Address addr;
Word wdata;
logic req, next_req;
logic we, next_we;
logic except_align;
logic res_valid;
Word res;
logic inst_valid_d;
logic bus_queue_empty;
Reg_index rt_d;


assign ir = inst.ir;
always_comb aa = opbus.opbus_0.a;
always_comb bb = opbus.opbus_0.b;
always_comb cc = opbus.opbus_0.c;

//---------------------------------------------------------------------------
// Address generation
//---------------------------------------------------------------------------

assign addr = aa + bb;
assign wdata = cc;

//---------------------------------------------------------------------------
// Decoding
//---------------------------------------------------------------------------

// set enable and request
always_comb begin
  OPCMP(ir)
    DEV_CTRL_OPS:
    begin
      next_en = 1'b1;
      next_req = 1'b1;
    end

    default:
    begin
      next_en = 1'b0;
      next_req = 1'b0;
    end
  ENDOPCMP
end

// set write enable
always_comb begin
  OPCMP(ir)
    OPX(Xop_ecowx):
      next_we = 1'b1;

    default:
      next_we = 1'b0;
  ENDOPCMP
end

// register to synchronize with operand fetch
always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    en <= 1'b0;
    req <= 1'b0;
    we <= 1'b0;
    inst_valid_d <= 1'b0;
    rt_d <= '0;
  end else begin
    en <= next_en;
    req <= next_req;
    we <= next_we;
    inst_valid_d <= inst.valid;
    rt_d <= ir.d.rt;
  end

//---------------------------------------------------------------------------
// Datapath
//---------------------------------------------------------------------------

/* XXX Bus access module that performs one access and write the result back
  * using the delayed wb interface. */

Bus_access #(
  .BYTE_ENABLED(1'b0),
  .QUEUE_DEPTH(8),
  .ISSUE_TO_WB_LATENCY(Frontend::dev_ctrl_latency)
) bus_access (
  .clk, .reset,
  .en(en),
  .gpr_dest(rt_d),
  .baddr(addr),
  .mode(Load_word),
  .exts(1'b0),
  .wdata,
  .req,
  .we,
  .result(res),
  .result_valid(res_valid),
  .iobus(iobus),
  .delayed_wb(dwb),
  .except_alignment(except_align),
  .pipe_empty(bus_queue_empty)
);

assign pipe_empty = bus_queue_empty & ~inst.valid & ~inst_valid_d;

always_comb begin
  resbus.res_a = res;
  resbus.res_b = '0;
  resbus.crf = '0;
  resbus.msr = '0;
  resbus.cout = 1'b0;
  resbus.ov = 1'b0;
  resbus.valid = res_valid;
end

`ifndef SYNTHESIS
  /* Test that no alignment exceptions occur. */
  check_alignment: assert property (
    @(posedge clk) disable iff(reset)
    ( !except_align )
  ) else $error("Alignment error on bus access -> Access is not executed.");
`endif /** SYNTHESIS */


endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
