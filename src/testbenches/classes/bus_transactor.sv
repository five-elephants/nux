// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef BUS_TRANSACTOR_SV__
`define BUS_TRANSACTOR_SV__

//---------------------------------------------------------------------------
// Bus handling class
//---------------------------------------------------------------------------

class Bus_transactor #(type Addr = int, type Data = int);
  virtual Bus_if #(.byteEn(1'b1)) intf = null;

  localparam int num_data_bytes = $bits(Data)/8;

  typedef logic[num_data_bytes-1:0] Data_byte_en;

  function new(virtual Bus_if #(.byteEn(1'b1)) intf);
    this.intf = intf;
    clear_request();
    intf.MRespAccept = 1'b0;
  endfunction

  function automatic void clear_request();
    intf.MCmd <= Bus::IDLE;
    intf.MAddr <= 0;
    intf.MData <= 0;
    intf.MDataValid <= 1'b0;
    intf.MByteEn <= '1;
  endfunction

  task automatic write(input Addr addr, Data data, Data_byte_en byte_en);
    intf.MCmd <= Bus::WR;
    intf.MAddr <= addr;
    intf.MData <= data;
    intf.MDataValid <= 1'b1;
    intf.MByteEn <= byte_en;
    intf.MRespAccept <= 1'b1;

    @(posedge intf.Clk);
    while( intf.SCmdAccept == 1'b0 ) @(posedge intf.Clk);

    clear_request();

    while( intf.SResp != Bus::DVA) @(posedge intf.Clk);    

    intf.MRespAccept <= 1'b0;
  endtask


  task automatic read(input Addr addr, Data_byte_en byte_en, output Data data);
    intf.MCmd <= Bus::RD;
    intf.MAddr <= addr;
    intf.MByteEn <= byte_en;
    intf.MRespAccept <= 1'b1;

    @(posedge intf.Clk);
    while( intf.SCmdAccept == 1'b0 ) @(posedge intf.Clk);

    clear_request();

    while( intf.SResp != Bus::DVA) @(posedge intf.Clk);    

    intf.MRespAccept <= 1'b0;
    data = intf.SData;
  endtask
endclass

`endif

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
