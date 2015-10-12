// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Bus::*;

interface Bus_if 
  #(// signal configuration options
    parameter bit addr = 1'b1,
    parameter int addr_width = 32,
    parameter bit data = 1'b1,
    parameter int data_width = 32,
    parameter bit datahandshake = 1'b0,
    parameter bit respaccept = 1'b1,
    parameter bit cmdaccept = 1'b1,
    parameter bit sdata = 1'b1,
    parameter bit dataaccept = 1'b0,
    parameter bit resp = 1'b1,
    parameter bit byteen = 1'b0,
    
    // protocol options
    parameter bit read_enable = 1'b1,       // enable the read command
    parameter bit write_enable = 1'b1,      // enable the write command
    parameter bit reqdata_together = 1'b1,  // request and datahandshake phases begin and end together
    parameter bit writeresp_enable = 1'b1   // a response is required for write commands
  )
  (input logic Clk);

  localparam num_bytes = data_width / 8;

  typedef logic[addr_width-1:0] Addr;
  typedef logic[data_width-1:0] Data;
  typedef logic[num_bytes-1:0] Byte_en;


  // basic signals
  logic     MReset_n;
  Addr      MAddr;
  Ocp_cmd   MCmd;
  Data      MData;
  logic     MRespAccept;
  logic     SCmdAccept;
  Data      SData;
  Ocp_resp  SResp;

  // simple extension
  Byte_en   MByteEn;

  
  modport master(
    `ifdef SYNTOOL_SYNPLIFY
      ref addr_width, data_width, byteen,
    `endif
    input Clk,
    output MReset_n,
    output MAddr, MCmd, MData, MRespAccept, MByteEn,
    input SCmdAccept, SData, SResp
  );
  modport slave(
    `ifdef SYNTOOL_SYNPLIFY
      ref addr_width, data_width, byteen,
    `endif
    input Clk, 
    input MReset_n,
    input MAddr, MCmd, MData, MRespAccept, MByteEn,
    output SCmdAccept, SData, SResp
  );

  `ifndef SYNTHESIS

  /** Request data must stay stable until SCmdAccept is asserted. */
  property request_stable;
    Ocp_cmd a_MCmd;
    Addr a_MAddr;
    Data a_MData;
    Byte_en a_MByteEn;

    @(posedge Clk) disable iff(!MReset_n)
    ( ((MCmd != Bus::IDLE) && !SCmdAccept, 
      a_MCmd = MCmd,
      a_MAddr = MAddr,
      a_MData = MData,
      a_MByteEn = MByteEn)
      |-> ((MCmd === a_MCmd && a_MAddr === MAddr && a_MData === MData) [* 1:$] 
        ##1 (SCmdAccept && MCmd === a_MCmd && a_MAddr === MAddr && a_MData === MData)) );
  endproperty

  check_request_stable: assert property (request_stable) else
    $error("Request data must stay stable until SCmdAccept is asserted");

  /** Response must stay stable until MRespAccept is asserted. */
  property response_stable;
    Ocp_resp a_SResp;
    Data a_SData;

    @(posedge Clk) disable iff(!MReset_n)
    ( ((SResp != Bus::NULL) && !MRespAccept,
      a_SResp = SResp,
      a_SData = SData)
      |-> ((SResp === a_SResp && SData === a_SData) [* 1:$]
        ##1 (MRespAccept && SResp === a_SResp && SData === a_SData)) );
  endproperty

  check_response_stable: assert property(response_stable) else
    $error("Response must stay stable until MRespAccept is asserted");

  /** MByteEn may only be used when byteen is set. */
  check_byteen_opt: assert property (
    @(posedge Clk) disable iff(byteen)
    ( $stable(MByteEn) ) 
  ) else $error("MByteEn may only change when byteen option is 1'b1");

  //---------------------------------------------------------------------------
  /** Number of requests must match the number of responses */
  //int num_in_flight;

  //always_ff @(posedge Clk or negedge MReset_n)
    //if( !MReset_n )
      //num_in_flight <= 0;
    //else begin
      //int inc;

      //inc = 0;
      //if( (MCmd != Bus::IDLE) && SCmdAccept )
        //inc = 1;

      //if( (SResp != Bus::NULL) && MRespAccept )
        //inc = inc -1;

      //num_in_flight <= num_in_flight + inc;
    //end

  //check_response_matches_to_request: assert property (
    //@(posedge Clk) disable iff(!MReset_n)
    //( ((SResp != Bus::NULL) && MRespAccept)
      //|-> (num_in_flight >= 0) )
  //) else
    //$error("Response without matching request was received");
  //---------------------------------------------------------------------------
  `endif  /* SYNTHESIS */
endinterface




// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
