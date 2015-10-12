// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/**
* The Msg_queue module is intended as communication channel between two
* processors using the OCP bus Bus_if. Data words are inserted into the queue
* when the writer writes to location ADDR_CHANNEL and taken from the queue when the
* reader reads from ADDR_CHANNEL.
* A read by the writer of location ADDR_STATUS returns the current flags. Same
* for the reader. */
module Msg_queue
  #(parameter int DEPTH = 16,
    parameter int DATA_WIDTH = 32,
    parameter int ADDR_CHANNEL = 0,
    parameter int ADDR_STATUS = 4)
  ( Bus_if.slave writer,
    Bus_if.slave reader );

//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

typedef logic[DATA_WIDTH-1:0] Data_in_t;
typedef logic[DATA_WIDTH-1:0] Data_out_t;

logic push;
logic next_pop, pop;
logic fifo_full;
logic fifo_almost_full;
logic fifo_empty;
logic fifo_half_full;
logic fifo_almost_empty;
logic fifo_error;
Data_in_t fifo_din;
Data_out_t fifo_dout;
Data_out_t next_SData;
logic next_dva;


//---------------------------------------------------------------------------
// Writer side
//---------------------------------------------------------------------------

assign fifo_din = writer.MData;

always_comb begin
  // default assignment
  push = 1'b0;
  writer.SCmdAccept = 1'b0;
  writer.SDataAccept = 1'b0;
  writer.SResp = Bus::NULL;

  if( (writer.MCmd == Bus::WR) && writer.MDataValid && !fifo_full ) begin
    push = 1'b1;
    writer.SCmdAccept = 1'b1;
    writer.SDataAccept = 1'b1;
    writer.SResp = Bus::DVA;  // XXX honor writer.SRespAccept
  end
end

assign writer.SData = 'x;

//---------------------------------------------------------------------------
// FIFO 
//---------------------------------------------------------------------------

// XXX Add configurable pipeline stage before FIFO

DW_fifo_s1_sf #(
  .depth(DEPTH),
  .width($bits(Data_in_t)),
  .ae_level(1),
  .af_level(1),
  .err_mode(0),
  .rst_mode(2)   // async reset without memory
) fifo (
  .clk(writer.Clk),
  .rst_n(writer.MReset_n),
  .push_req_n(~push),
  .pop_req_n(~pop),
  .diag_n(1'b1),
  .data_in(fifo_din),
  .empty(fifo_empty),
  .almost_empty(fifo_almost_empty),
  .half_full(fifo_half_full),
  .almost_full(fifo_almost_full),
  .full(fifo_full),
  .error(fifo_error),
  .data_out(fifo_dout)
);


//---------------------------------------------------------------------------
// Reader side
//---------------------------------------------------------------------------

//assign reader.SData = fifo_dout;

always_comb begin
  // default assignments
  next_pop = 1'b0;
  next_dva = 1'b0;
  reader.SCmdAccept = 1'b0;
  reader.SDataAccept = 1'b0;
  next_SData = fifo_dout;

  if( reader.MCmd == Bus::RD ) begin
    unique case(reader.MAddr[1:0])
      2'b00: begin
        if( !fifo_empty ) begin
          next_pop = 1'b1;
          next_dva = 1'b1;
          reader.SCmdAccept = 1'b1;
          reader.SDataAccept = 1'b1;
          next_SData = fifo_dout;
        end
      end

      2'b01: begin
        reader.SCmdAccept = 1'b1;
        reader.SDataAccept = 1'b1;
        next_SData = { {DATA_WIDTH-1{1'b0}}, fifo_empty };
        next_dva = 1'b1;
      end

      2'b10: begin
        reader.SCmdAccept = 1'b1;
        reader.SDataAccept = 1'b1;
        next_SData = { {DATA_WIDTH-1{1'b0}}, fifo_full};
        next_dva = 1'b1;
      end

      2'b11: begin
        reader.SCmdAccept = 1'b1;
        reader.SDataAccept = 1'b1;
        next_SData = { 
          {DATA_WIDTH-6{1'b0}}, 
          fifo_full, 
          fifo_almost_full,
          fifo_half_full,
          fifo_almost_empty,
          fifo_empty,
          fifo_error
        };
        next_dva = 1'b1;
      end

      default: begin
        reader.SCmdAccept = 1'bx;
        reader.SDataAccept = 1'bx;
        next_SData = 'x;
        next_pop = 1'bx;
        next_dva = 1'bx;
      end
    endcase
  end

  //if( (reader.MCmd == Bus::RD) && !fifo_empty ) begin
    //next_pop = 1'b1;
    //reader.SCmdAccept = 1'b1;
    //reader.SDataAccept = 1'b1;
  //end
end

always_ff @(posedge reader.Clk or negedge reader.MReset_n)
  if( !reader.MReset_n ) begin
    reader.SResp <= Bus::NULL;
    pop <= 1'b0;
    reader.SData <= '0;
  end else begin
    pop <= next_pop;
    reader.SData <= next_SData;

    if( next_dva )
      reader.SResp <= Bus::DVA;
    else
      reader.SResp <= Bus::NULL;
  end

// XXX honor reader.SRespAccept 

endmodule



// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
