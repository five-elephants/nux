// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Module to detect interrupt conditions.
*
* Detected interrupts are signaled to the processor, where the int_sched
* module checks internal interrupt masks and starts the execution according to
* the priority table.
* This interrupt controller has to wake the processor if necessary */
module Interrupt_ctrl
  ( input logic clk, reset,

    Pu_ctrl_if.ctrl    pu_ctrl,
    //Processor_if.proc  ctrl,
	input logic        doorbell,
    Timer_if.int_ctrl  timer,

    output logic       en_clk,

    input Pu_types::Word gin
  );

import Pu_types::*;

//---------------------------------------------------------------------------
// Local types
//---------------------------------------------------------------------------

typedef enum logic[2:0] {
  S_IDLE   = 3'b001,
  S_SLEEP  = 3'b010,
  S_WAKEUP = 3'b100,
  S_UNDEF  = 3'bxxx
} State;


//---------------------------------------------------------------------------
// Local signals
//---------------------------------------------------------------------------

State      state;
logic      doorbell_d;
logic      doorbell_req;

logic      pin_int, pin_int_req;
logic      pin_int_vec[DWIDTH-1:0];
Word       gin_d;
Word       gin_mask;           /**< enable/disable pins individually */
Word       gin_sense_level;    /**< 1: trigger on level, 0: trigger on edge */
Word       gin_trigger;        /**< 0: high level or rising edge, 1: low level or falling edge */

logic      timer_req;

// static default configuration
assign 
  gin_mask[31:4] = '0,
  gin_mask[3:0] = pu_ctrl.iccr.gin_mask,
  gin_sense_level[31:4] = '1,
  gin_sense_level[3:0] = pu_ctrl.iccr.gin_sense_level,
  gin_trigger[31:4] = '0,
  gin_trigger[3:0] = pu_ctrl.iccr.gin_trigger;

//---------------------------------------------------------------------------
// State machine
//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
  if( reset )
    state <= S_IDLE;
  else 
    unique case(state)
      S_IDLE: begin
        if( pu_ctrl.sleep )
          state <= S_SLEEP;
      end

      S_SLEEP: begin
        if( !pu_ctrl.sleep )
          state <= S_IDLE;
        else if( /*pu_ctrl.msr_ee 
            &&*/ (doorbell_req 
              || pin_int_req
              || timer_req) )
          state <= S_WAKEUP;
      end

      S_WAKEUP: begin
        if( !pu_ctrl.sleep )
          state <= S_IDLE;
      end

      default:
        state <= S_UNDEF;
    endcase


always_comb begin
  // default assignments
  pu_ctrl.wakeup = 1'b0;
  en_clk = 1'b0;

  unique case(state)
    S_IDLE: begin
    end

    S_SLEEP: begin
    end

    S_WAKEUP: begin
      pu_ctrl.wakeup = 1'b1;
      en_clk = 1'b1;
    end

    default: begin
      pu_ctrl.wakeup = 1'bx;
      en_clk = 1'bx;
    end
  endcase
end

assign
  pu_ctrl.doorbell = doorbell_req,
  pu_ctrl.ext_input = pin_int_req;

assign timer_req = ((timer.tcr.die && timer.tsr.dis)
    || (timer.tcr.fie && timer.tsr.fis)) && !pu_ctrl.other_ack;

//---------------------------------------------------------------------------
always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    doorbell_d <= 1'b0;
    doorbell_req <= 1'b0;
  end else begin
    doorbell_d <= doorbell;

    if( pu_ctrl.doorbell_ack || !pu_ctrl.msr_ee )
      doorbell_req <= 1'b0;
    else
      doorbell_req <= (doorbell & ~doorbell_d) | doorbell_req;
  end

//---------------------------------------------------------------------------
// Pin interrupt trigger logic
//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    gin_d <= '0;
    pin_int_req <= 1'b0;
  end else begin
    gin_d <= gin;

    if( pu_ctrl.ext_input_ack || !pu_ctrl.msr_ee )
      pin_int_req <= 1'b0;
    else
      pin_int_req <= pin_int | pin_int_req;
  end

generate
  genvar pin_i;

  logic next_pin_int_vec[DWIDTH-1:0];

  for(pin_i=0; pin_i<DWIDTH; pin_i++) begin : gen_pin_trigger
    /** Detect interrupt requests on pins */
    always_comb begin
      if( gin_sense_level[pin_i] )
        next_pin_int_vec[pin_i] = gin[pin_i] ^ gin_trigger[pin_i];
      else
        next_pin_int_vec[pin_i] = (~gin_d[pin_i] ^ gin_trigger[pin_i]) 
            & (gin[pin_i] ^ gin_trigger[pin_i]);
    end

    always_ff @(posedge clk or posedge reset)
      if( reset )
        pin_int_vec[pin_i] <= 1'b0;
      else
        pin_int_vec[pin_i] <= next_pin_int_vec[pin_i];

  end : gen_pin_trigger
endgenerate

//assign pin_int = (| (pin_int_vec & gin_mask));
always_comb
begin
  pin_int = 1'b0;
  for(int i=0; i<$bits(pin_int_vec); i++)
    pin_int = pin_int | (pin_int_vec[i] & gin_mask[i]);
end

endmodule
