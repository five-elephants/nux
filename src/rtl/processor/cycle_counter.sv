// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


//---------------------------------------------------------------------------
module Cycle_counter
  ( input logic clk, reset,
    input Frontend::Seq_ctr stop_val,
    input logic jump_ignore,
    input logic is_multicycle,
    //input logic issue,
    input logic hold_stream,
    output Frontend::Seq_ctr cur_val,
    output logic hold);

  import Frontend::*;

  //---------------------------------------------------------------------------
  // Local types and signals
  //---------------------------------------------------------------------------

  typedef enum logic[1:0] {
    S_IDLE  = 2'b01,
    S_COUNT = 2'b10,
    S_UNDEF = 2'bxx
  } State;

  State state;
  Seq_ctr ctr, next_ctr;
  logic done_i;


  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      state <= S_IDLE;
      ctr <= '0;
    end else
      unique case(state)
        S_IDLE: begin
          if( is_multicycle && !jump_ignore ) begin
            state <= S_COUNT;
            if( !hold_stream )
              ctr <= ctr + 1;
          end
        end

        S_COUNT: begin
          if( jump_ignore ) begin
            state <= S_IDLE;
            ctr <= '0;
          end else if( !hold_stream ) begin
            if( ctr == stop_val ) begin
              state <= S_IDLE;
              ctr <= '0;
            end else begin
              ctr <= ctr + 1;
            end
          end
        end
              
        default:
          state <= S_UNDEF;
      endcase

  always_comb begin
    // default assignment
    hold = 1'b0;
    cur_val = ctr;

    unique case(state)
      S_IDLE: begin
        if( is_multicycle && !jump_ignore )
          hold = 1'b1;
      end

      S_COUNT: begin
        if( jump_ignore || (/*issue &&*/ (ctr == stop_val)) )
          hold = 1'b0;
        else
          hold = 1'b1;
      end

      default: begin
        hold = 1'bx;
      end
    endcase
  end

endmodule
//---------------------------------------------------------------------------



// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
