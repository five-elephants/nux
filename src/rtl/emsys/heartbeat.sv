// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module Heartbeat
  #(parameter int CYCLES_PER_SEC = 100000000,
    parameter int PULSE_CYCLES   =  10000000 )
  ( input logic clk, reset,
    output logic led );


int beat_ctr, pulse_ctr;


always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    beat_ctr <= 0;
    pulse_ctr <= 0;
  end else begin
    if( beat_ctr == CYCLES_PER_SEC ) begin
      pulse_ctr <= 0;
      beat_ctr <= 0;
    end else begin
      beat_ctr <= beat_ctr +1;
    end

    if( pulse_ctr != PULSE_CYCLES )
      pulse_ctr <= pulse_ctr +1;
  end

assign led = !(pulse_ctr == PULSE_CYCLES);

endmodule




// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
