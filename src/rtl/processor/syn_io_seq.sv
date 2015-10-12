// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Syn_io_seq
  ( input logic clk, reset,
    Syn_io_if.client syn_io,
    input logic start,
    input Pu_types::Word seq,
    input Pu_types::Word addr,
    output logic busy);

  import Syn_io::*;

  typedef enum logic[2:0] {
    S_IDLE  = 3'b001,
    S_START = 3'b010,
    S_WAIT  = 3'b100,
    S_UNDEF = 3'bxxx
  } State;

  typedef Opcd[0:7] Op_seq;

  State state;
  Op_seq op_seq;
  logic[2:0] ctr;
  Pu_types::Word addr_reg;


  always_ff @(posedge clk or posedge reset)
    if( reset )
      state <= S_IDLE;
    else
      unique case(state)
        S_IDLE: begin
          if( start )
            //state <= S_START;
            state <= S_WAIT;
        end

        S_START: begin
          state <= S_WAIT;
        end

        S_WAIT: begin
          if( !syn_io.busy )
            if( (ctr == 7) || (op_seq[ctr+1] == OP_IDLE) )
              state <= S_IDLE;
            else
              state <= S_WAIT;
        end

        default: begin
          state <= S_UNDEF;
        end
      endcase

  always_comb begin
    // default assignment
    syn_io.start = 1'b0;
    syn_io.op.opcd = OP_IDLE;
    syn_io.op.row = 0;
    syn_io.op.colset = 0;
    busy = 1'b0;

    unique case(state)
      S_IDLE: begin
        if( start ) begin
          syn_io.start = 1'b1;
          syn_io.op.opcd = Opcd'(seq[31:28]);
          {syn_io.op.row, syn_io.op.colset} = addr[$bits(Row_addr)+$bits(Colset_addr)-1:0];
        end
      end

      S_START: begin
        syn_io.start = 1'b1;
        syn_io.op.opcd = op_seq[ctr];
        {syn_io.op.row, syn_io.op.colset} = addr_reg[$bits(Row_addr)+$bits(Colset_addr)-1:0];
        busy = 1'b1;
      end

      S_WAIT: begin
        {syn_io.op.row, syn_io.op.colset} = addr_reg[$bits(Row_addr)+$bits(Colset_addr)-1:0];
        syn_io.op.opcd = op_seq[ctr];
        //busy = 1'b1;
        busy = syn_io.busy;

        if( !syn_io.busy && !((ctr == 7) || (op_seq[ctr+1] == OP_IDLE)) ) begin
          syn_io.start = 1'b1;
          syn_io.op.opcd = op_seq[ctr+1];
          busy = 1'b1;
        end
      end
    endcase
  end

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      ctr <= 0;
      op_seq <= '0;
      addr_reg <= addr;
    end else begin
      if( state == S_IDLE ) begin
        ctr <= 0;
        if( start ) begin
          op_seq <= seq;
          addr_reg <= addr;
        end
      end else if( (state == S_WAIT) && !syn_io.busy ) begin
        ctr <= ctr + 1;
      end
    end

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
