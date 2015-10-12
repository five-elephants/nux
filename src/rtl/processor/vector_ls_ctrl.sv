// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_ls_ctrl
  #(parameter int NUM_SLICES = 1,
    parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int SCALAR_SIZE = 32)
  ( input logic clk, reset,
    input logic valid,
    input Pu_inst::Fxv_opcd xo,
    input Pu_types::Word g,
    output logic result_avail,
    Vector_ls_ctrl_if.ctrl ctrl,
    output logic ready );


  localparam int VECTOR_SIZE = NUM_ELEMS * ELEM_SIZE;
  localparam int SCALARS_PER_VECTOR = VECTOR_SIZE / SCALAR_SIZE;
  localparam int NUM_SCALARS = SCALARS_PER_VECTOR * NUM_SLICES;


  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------
  
  typedef enum logic[2:0] {
    S_IDLE          = 3'b000,
    S_LOADING       = 3'b001,
    S_LOAD_COMPLETE = 3'b010,
    S_STORING       = 3'b100,
    S_UNDEF         = 3'bxxx
  } State;


  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------
  
  State state;


  //--------------------------------------------------------------------------------
  // Control state machine
  //--------------------------------------------------------------------------------

  always_ff @(posedge clk or posedge reset)
    if( reset ) 
      state <= S_IDLE;
    else
      unique case(state)
        S_IDLE: begin
          if( valid && (xo == Pu_inst::Xop_fxvlax) )
            state <= S_LOADING;
          else if( valid && (xo == Pu_inst::Xop_fxvstax) )
            state <= S_STORING;
        end

        S_LOADING: begin
          if( ctrl.complete )
            state <= S_LOAD_COMPLETE;
        end

        S_LOAD_COMPLETE: begin
          state <= S_IDLE;
        end

        S_STORING: begin
          if( ctrl.complete )
            state <= S_IDLE;
        end

        default:
          state <= S_UNDEF;
      endcase


  always_comb begin : control_fsm_outputs
    // default assignments
    ctrl.new_op = 1'b0;
    ctrl.store_en = 1'b0;
    ctrl.we = 1'b0;
    ctrl.count = NUM_SCALARS;
    ctrl.g = g;
    result_avail = 1'b0;
    ready = 1'b1;

    unique case(state)
      S_IDLE: begin
        if( valid && (xo == Pu_inst::Xop_fxvlax) ) begin
          ctrl.new_op = 1'b1;
          //ready = 1'b0;
        end else if( valid && (xo == Pu_inst::Xop_fxvstax) ) begin
          ctrl.new_op = 1'b1;
          ctrl.we = 1'b1;
          ctrl.store_en = 1'b1;
          //ready = 1'b0;
        end
      end

      S_LOADING: begin
        ready = 1'b0;
      end

      S_LOAD_COMPLETE: begin
        result_avail = 1'b1;
        ready = 1'b0;
      end

      S_STORING: begin
        ready = 1'b0;
        ctrl.we = 1'b1;

        if( ctrl.complete )
          result_avail = 1'b1;
      end

      default: begin
      end
    endcase
  end
  
   

endmodule

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
