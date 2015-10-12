// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Fub_load_store
  ( input logic clk, reset,
    input Frontend::Issue_slot inst,
    Operand_if.read opbus,
    output Backend::Result_bus resbus,
    
    Ram_if.client dmem,
    Int_sched_if.load_store int_sched_if );

import Pu_types::*;
import Backend::*;


Address data_address;
Word data_din;

Load_store_ctrl_if ctrl();
//Load_store_data_if data(data_address, data_din);

Address pc_d, pc_d2;
Result_bus resbus_i;

Dec_load_store decode (
  .clk, .reset,
  .inst,
  .ctrl
);

assign data_address = opbus.opbus_0.a + opbus.opbus_0.b;
assign data_din = opbus.opbus_0.c;

Load_store load_store (
  .clk(clk),
  .reset(reset),
  .ctrl(ctrl.load_store),
  //.data(data.load_store),
  .address(data_address),
  .din(data_din),
  .dmem(dmem),
  .except(int_sched_if),
  .result(resbus_i)
);

always_ff @(posedge clk)
begin
  pc_d <= inst.pc;
end

assign int_sched_if.pc_alignment = pc_d;

generate if( Frontend::ls_latency == 2 ) begin : gen_low_latency

  always_comb begin
    pc_d2 = pc_d;
    resbus = resbus_i;
  end
  
end : gen_low_latency
else if( Frontend::ls_latency == 3 )
begin : gen_normal

  always_ff @(posedge clk)
  begin
    pc_d2 <= pc_d;
    resbus <= resbus_i;
  end

end : gen_normal
endgenerate
endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
