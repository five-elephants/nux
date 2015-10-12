// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module Jtag_to_mem
  ( Ram_if.client     imem,
    Ram_if.client     dmem,
    Processor_if.proc jtag );

//---------------------------------------------------------------------------
assign
  imem.en = jtag.imem_re | jtag.imem_we,
  imem.addr = jtag.imem_addr,
  imem.data_w = jtag.imem_data_w,
  imem.we = jtag.imem_we,
  imem.be = 4'b1111;
assign
  jtag.imem_data_r = imem.data_r;


assign
  dmem.en = jtag.dmem_re | jtag.dmem_we,
  dmem.addr = jtag.dmem_addr,
  dmem.data_w = jtag.dmem_data_w,
  dmem.we = jtag.dmem_we,
  dmem.be = 4'b1111;
assign
  jtag.dmem_data_r = dmem.data_r;
//---------------------------------------------------------------------------

endmodule
