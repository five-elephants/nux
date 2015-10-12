// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Fub_ls_var
  ( input logic clk, reset,
    input Frontend::Issue_slot inst,
    input Frontend::Predecoded predec,
    Operand_if.read opbus,
    output Backend::Result_bus resbus,
    Int_sched_if.load_store int_sched_if,

    Bus_if.master iobus,

    Delayed_wb_if.fub dwb,
    output logic pipe_empty );

import Pu_inst::*;
import Pu_types::*;
import Backend::*;

//---------------------------------------------------------------------------
// Local types & signals
//---------------------------------------------------------------------------

Load_store_ctrl_if ctrl();

Inst ir;
Word aa, bb, cc;
logic en, next_en;
logic exts;
Address addr;
Address addr_d;
logic wb_addr_d;
Word wdata;
logic req, next_req;
logic we, next_we;
logic except_align;
logic res_valid;
Word res;
Address pc_d;
logic inst_valid_d;
logic bus_queue_empty;
Reg_index rt_d;
logic addr_cycle;
logic read_ra_d;


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

Dec_ls_var decode (
  .clk, .reset,
  .inst,
  .ctrl(ctrl.decode)
);

always_ff @(posedge clk)
begin
  inst_valid_d <= inst.valid;
  pc_d <= inst.pc;
  wb_addr_d <= ~ctrl.return_dout & ctrl.en;
  rt_d <= predec.rt;
  read_ra_d <= predec.read_ra;

  // register address for second part of update instruction to avoid races
  if( inst_valid_d && read_ra_d ) begin
    addr_d <= addr;
  end
end

//---------------------------------------------------------------------------
// Datapath
//---------------------------------------------------------------------------

/* Bus access module that performs one access and write the result back
 * using the delayed wb interface. */
Bus_access #(
  .QUEUE_DEPTH(16),
  .ISSUE_TO_WB_LATENCY(Frontend::ls_bus_latency)
) bus_access (
  .clk, .reset,
  .en(ctrl.en),
  .gpr_dest(rt_d),
  .baddr(addr),
  .mode(ctrl.ls_mode),
  .exts(ctrl.exts),
  .wdata,
  .req(ctrl.do_request),
  .we(ctrl.ls_we),
  .result(res),
  .result_valid(res_valid),
  .iobus,
  .delayed_wb(dwb),
  .except_alignment(except_align),
  .pipe_empty(bus_queue_empty)
);

always_comb begin
  if( wb_addr_d ) begin
    resbus.res_a = addr_d;
    resbus.valid = 1'b1;
  end else begin
    resbus.res_a = res;
    resbus.valid = res_valid;
  end
  resbus.res_b = '0;
  resbus.crf = '0;
  resbus.msr = '0;
  resbus.cout = 1'b0;
  resbus.ov = 1'b0;
end

assign 
  int_sched_if.base_alignment = except_align,
  int_sched_if.pc_alignment = pc_d;

assign pipe_empty = bus_queue_empty & ~inst.valid & ~inst_valid_d;

endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
