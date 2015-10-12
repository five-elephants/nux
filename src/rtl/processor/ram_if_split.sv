// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Ram_if_split
  #(parameter int SELECT_BIT = 31)
  ( input logic clk,
    Ram_if.client top,
    Ram_if.memory out_0,
    Ram_if.memory out_1 );

  logic sel_d;

  // Forwarding request to selected output leaf
  always_comb begin
    // default assignment
    out_0.en = 1'b0;
    out_0.addr = top.addr;
    out_0.data_w = top.data_w;
    out_0.we = 1'b0;
    out_0.be = top.be;
    out_1.en = 1'b0;
    out_1.addr = top.addr;
    out_1.data_w = top.data_w;
    out_1.we = 1'b0;
    out_1.be = top.be;
   
    if( top.addr[SELECT_BIT] == 1'b1 ) begin
      out_1.en = top.en;
      out_1.we = top.we;
    end else begin
      out_0.en = top.en;
      out_0.we = top.we;
    end
  end

  // registering selection
  always_ff @(posedge clk)
    if( top.en )
      sel_d <= top.addr[SELECT_BIT];

  // forwarding response to root node multiplexing on the registered selection
  always_comb
    if( sel_d == 1'b1 ) begin
      top.data_r = out_1.data_r;
      top.delay = out_1.delay;
    end else begin
      top.data_r = out_0.data_r;
      top.delay = out_0.delay;
    end

endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
