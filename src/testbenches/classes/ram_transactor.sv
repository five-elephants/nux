// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef RAM_TRANSACTOR_SV__
`define RAM_TRANSACTOR_SV__

class Ram_transactor #(type Addr = int, type Data = int);
  virtual Ram_if #(.ADDR_WIDTH($bits(Addr)), .DATA_WIDTH($bits(Data))) intf = null;
  time clk_period = 10ns;

  localparam int num_data_bytes = $bits(Data)/8;
  typedef logic[num_data_bytes-1:0] Data_byte_en;

  function new(virtual Ram_if #(.ADDR_WIDTH($bits(Addr)), .DATA_WIDTH($bits(Data))) intf, input time clk_period);
    this.intf = intf;
    this.clk_period = clk_period;
    clear_request();
  endfunction

  function automatic void clear_request();
    intf.en <= 1'b0;
    intf.be <= '0;
    intf.we <= 1'b0;
    intf.addr <= '0;
    intf.data_w <= '0;
  endfunction

  task automatic write(input Addr addr, Data data, Data_byte_en byte_en);
    //@(negedge clk_event);
    intf.en <= 1'b1;
    intf.be <= byte_en;
    intf.we <= 1'b1;
    intf.data_w <= data;
    intf.addr <= addr;
    
    #(clk_period);
    //@(negedge clk_event);
    clear_request();
  endtask

  task automatic read(input Addr addr, Data_byte_en byte_en, output Data data);
    //@(negedge clk_event);
    intf.en <= 1'b1;
    intf.be <= byte_en;
    intf.we <= 1'b0;
    intf.data_w <= '0;
    intf.addr <= addr;

    #(clk_period);
    //@(negedge clk_event);
    while( intf.delay ) #(clk_period);
    //while( intf.delay ) @(negedge clk_event);
    data = intf.data_r;

    clear_request();
  endtask
endclass

`endif

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
