// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Iobus_dummy
  #(parameter int RD_ACCEPT_LATENCY = 0,
    parameter int WR_ACCEPT_LATENCY = 0,
    parameter int RD_RETURN_LATENCY = 1,
    parameter int WR_RETURN_LATENCY = 1,
    parameter int RESPONSE_FUNCTION = 0,  // 0 - STATIC return a static 32'h1
                                          // 1 - MEM return what was previously written
                                          // 2 - ZERO return a static 32'h0
                                          // 3 - ADDR return address
    parameter int DATA_WIDTH = 32,
    parameter int ADDR_WIDTH = 32,
    parameter bit BYTE_ENABLED = 1'b0,
    parameter logic[DATA_WIDTH-1:0] MEM_DEFAULT = 'x)
  ( input logic clk, reset,
    Bus_if.slave iobus );

import std::*;

//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

typedef enum int {
  FUNC_STATIC = 0,
  FUNC_MEM    = 1,
  FUNC_ZERO   = 2,
  FUNC_ADDR   = 3
} Function;

typedef logic[DATA_WIDTH-1:0] Data;
typedef logic[ADDR_WIDTH-1:0] Addr;
typedef logic[(DATA_WIDTH/8)-1:0] Byte_enable;

Bus::Ocp_cmd MCmd;
Addr MAddr;
Data MData;
Byte_enable MByteEn;

int accept_ctr;
int return_ctr;

// associative array for memory
Data mem[Addr];

//---------------------------------------------------------------------------
// Local functions
//---------------------------------------------------------------------------

function automatic Data byte_en_mask(input Byte_enable be);
  Data rv;

  for(int i=0; i<$bits(be); i++)
    rv[8*(i+1)-1 -: 8] = {8{be[i]}};

  return rv;
endfunction

//---------------------------------------------------------------------------
function automatic Data response_data(input Bus::Ocp_cmd MCmd, Addr MAddr, Data MData, Byte_enable MByteEn);
  Data rv;

  unique case(RESPONSE_FUNCTION)
    FUNC_STATIC: 
      if( MCmd == Bus::WR )
        rv = '0;
      else
        rv = 1;

    FUNC_MEM:
      if( MCmd == Bus::WR ) begin
        rv = '0;
        if( BYTE_ENABLED ) begin
          if( mem.exists(MAddr) )
            mem[MAddr] = (MData & byte_en_mask(MByteEn)) | (mem[MAddr] & ~byte_en_mask(MByteEn));
          else
            mem[MAddr] = (MData & byte_en_mask(MByteEn)) | (MEM_DEFAULT & ~byte_en_mask(MByteEn));
        end else
          mem[MAddr] = MData;
      end else begin
        if( mem.exists(MAddr) )
          if( BYTE_ENABLED )
            rv = mem[MAddr] & byte_en_mask(MByteEn);
          else
            rv = mem[MAddr];
        else
          rv = MEM_DEFAULT;
      end

    FUNC_ZERO:
      rv = '0;

    FUNC_ADDR:
      rv = MAddr;
  endcase

  //$display("iobus_dummy: responding to request %s for address 0x%08h with data 0x%08h; rv = 0x%08h",
    //(MCmd == Bus::WR) ? "WR" : "RD", MAddr, MData, rv);

  return rv;
endfunction
//---------------------------------------------------------------------------
task automatic respond(ref semaphore sem_accept, sem_response, 
    input Bus::Ocp_cmd MCmd, Addr MAddr, Data MData, Byte_enable MByteEn);
  //$display("%8d: starting respond thread", $time);

  if( MCmd == Bus::RD ) 
    for(int i=0; i<RD_ACCEPT_LATENCY; i++) @(posedge clk);
  else if( MCmd == Bus::WR )
    for(int i=0; i<WR_ACCEPT_LATENCY; i++) @(posedge clk);

  @(negedge clk);
  sem_accept.get();
  iobus.SCmdAccept = 1'b1;
  //$display("%8d: SCmdAccept", $time);
  @(negedge clk) iobus.SCmdAccept = 1'b0;
  sem_accept.put();

  if( MCmd == Bus::RD ) 
    for(int i=0; i<RD_RETURN_LATENCY; i++) @(posedge clk);
  else if( MCmd == Bus::WR )
    for(int i=0; i<WR_RETURN_LATENCY; i++) @(posedge clk);

  @(negedge clk);
  //$display("%8d: DVA", $time);
  sem_response.get();
  iobus.SResp = Bus::DVA;
  iobus.SData = response_data(MCmd, MAddr, MData, MByteEn);

  while( !iobus.MRespAccept ) @(posedge clk);

  @(negedge clk);
  iobus.SResp = Bus::NULL;
  iobus.SData = '0;
  sem_response.put();

  //$display("%8d: response complete", $time);
endtask
//---------------------------------------------------------------------------

//always @(posedge reset)
  //if( reset ) begin
    //iobus.SCmdAccept <= 1'b0;
    //iobus.SDataAccept <= 1'b1;
    //iobus.SData <= '0;
    //iobus.SResp <= Bus::NULL;
  //end
  
initial begin
  semaphore sem_accept;
  semaphore sem_response;

  sem_accept = new (1);
  sem_response = new (1);

  iobus.SCmdAccept <= 1'b0;
  iobus.SData <= '0;
  iobus.SResp <= Bus::NULL;

  forever begin
    //$display("%8d: waiting for bus activity", $time);
    //@(iobus.MCmd or iobus.MAddr or iobus.MData or posedge iobus.Clk);
    @(posedge iobus.Clk);
    #1;
    if( iobus.MCmd != Bus::IDLE ) begin
      //$display("bus transaction");
      fork
        respond(sem_accept, sem_response, iobus.MCmd, iobus.MAddr, iobus.MData, iobus.MByteEn);
      join_none

      //@(negedge clk);
      //#(1ps);
      @(negedge clk);
      //$display("done");
    end
  end
end

always @(posedge reset)
begin
  mem.delete();
end

//---------------------------------------------------------------------------

//always_ff @(posedge clk or posedge reset)
  //if( reset ) begin
    //iobus.SDataAccept <= 1'b1;

    //accept_ctr <= -1;
    //return_ctr <= -1;
  //end else begin
    //if( accept_ctr == -1 && return_ctr <= 0 ) begin : start_request 
      //if( iobus.MCmd == Bus::RD ) begin
        //accept_ctr <= RD_ACCEPT_LATENCY-1;
        //return_ctr <= RD_RETURN_LATENCY-1;
      //end else if( iobus.MCmd == Bus::WR ) begin
        //accept_ctr <= WR_ACCEPT_LATENCY-1;
        //return_ctr <= WR_RETURN_LATENCY-1;
      //end else if( return_ctr == 0 )
        //return_ctr <= -1;
    //end else begin : finish_request
      //if( accept_ctr > -1 )
        //accept_ctr <= accept_ctr -1;

      //if( (return_ctr == 0 && iobus.MRespAccept) || (return_ctr > 0) )
        //return_ctr <= return_ctr -1;
    //end
  //end

//always_comb begin
  //bit accept;

  //// default assignments
  //iobus.SCmdAccept = 1'b0;
  //iobus.SResp = Bus::NULL;
  //iobus.SData = '0;
  //accept = 1'b0;

  //if( return_ctr <= 0 ) begin
    //if( iobus.MCmd == Bus::RD && RD_ACCEPT_LATENCY == 0 ) begin
      //iobus.SCmdAccept = 1'b1;
      //accept = 1'b1;
    //end else if( iobus.MCmd == Bus::WR && WR_ACCEPT_LATENCY == 0 ) begin
      //iobus.SCmdAccept = 1'b1;
      //accept = 1'b1;
    //end else if( accept_ctr == 0 ) begin
      //iobus.SCmdAccept = 1'b1;
      //accept = 1'b1;
    //end
  //end

  //if( accept ) begin
    //MCmd = iobus.MCmd;
    //MAddr = iobus.MAddr;
    //MData = iobus.MData;
  //end

  //if( MCmd == Bus::RD && RD_RETURN_LATENCY == 0 ) begin
    //iobus.SResp = Bus::DVA;
    //iobus.SData = response_data();
  //end else if( MCmd == Bus::WR && WR_RETURN_LATENCY == 0 ) begin
    //iobus.SResp = Bus::DVA;
    //iobus.SData = response_data();
  //end else if( return_ctr == 0 ) begin
    //iobus.SResp = Bus::DVA;
    //iobus.SData = response_data();
  //end
//end


endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
