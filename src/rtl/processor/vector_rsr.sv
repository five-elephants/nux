// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_rsr
  #(parameter int MULT_STAGES = 1,
    parameter int ADD_STAGES = 1)
  ( input logic clk, reset,
    input logic insert,
    input Vector::Vrf_index dests[0:3],
    output logic free,

    output Vector::Vrf_index vrf_addr,
    output logic vrf_en,
    output logic vrf_we );

  localparam int NUM_STAGES = MULT_STAGES + ADD_STAGES + 2;
  //localparam int TAPS[0:NUM_STAGES-1] = '{
    //0: 1,
    //MULT_STAGES: 2,
    //default: -1
  //};

  //--------------------------------------------------------------------------------
  // Local types and signals
  //--------------------------------------------------------------------------------
  
  typedef struct packed {
    logic en;
    logic we;
    Vector::Vrf_index addr;
  } Vrf_config;


  Vrf_config stages[0:NUM_STAGES-1];
  Vrf_config next_config[0:3];

  
  //--------------------------------------------------------------------------------
  // Input
  //--------------------------------------------------------------------------------
  
  always_comb begin
    next_config[0].en = 1'b1;
    next_config[0].we = 1'b0;
    next_config[0].addr = dests[0];

    next_config[1].en = 1'b1;
    next_config[1].we = 1'b0;
    next_config[1].addr = dests[1];

    next_config[2].en = 1'b1;
    next_config[2].we = 1'b0;
    next_config[2].addr = dests[2];

    next_config[3].en = 1'b1;
    next_config[3].we = 1'b1;
    next_config[3].addr = dests[3];
  end


  //--------------------------------------------------------------------------------
  // Shift stages
  //--------------------------------------------------------------------------------

  generate
    genvar stage_i;
    for(stage_i=0; stage_i<NUM_STAGES; stage_i++) begin : gen_stages
      if( stage_i == 0 ) begin : gen_output_stage

        always_ff @(posedge clk or posedge reset)
          if( reset ) begin
            stages[stage_i].en <= 1'b0;
          end else begin
            if( insert )
              stages[stage_i] <= next_config[1];
            else
              stages[stage_i] <= stages[stage_i+1];
          end

      end : gen_output_stage
      else if( stage_i == MULT_STAGES ) begin : gen_mult_input_stage

        always_ff @(posedge clk or posedge reset)
          if( reset ) begin
            stages[stage_i].en <= 1'b0;
          end else begin
            if( insert )
              stages[stage_i] <= next_config[2];
            else
              stages[stage_i] <= stages[stage_i+1];
          end

      end : gen_mult_input_stage
      else if( stage_i < NUM_STAGES-1 ) begin : gen_interim_stage

        always_ff @(posedge clk or posedge reset)
          if( reset ) begin
            stages[stage_i].en <= 1'b0;
          end else begin
            stages[stage_i] <= stages[stage_i+1];
          end

      end : gen_interim_stage
      else
      begin : gen_input_stage
        
        always_ff @(posedge clk or posedge reset)
          if( reset ) begin
            stages[stage_i].en <= 1'b0;
          end else begin
            if( insert )
              stages[stage_i] <= next_config[3];
            else
              stages[stage_i] <= '0;
          end

      end : gen_input_stage
    end : gen_stages
  endgenerate


  //--------------------------------------------------------------------------------
  // shifter output
  //--------------------------------------------------------------------------------
  
  always_comb begin
    if( insert ) begin
      vrf_en = next_config[0].en;
      vrf_we = next_config[0].we;
      vrf_addr = next_config[0].addr;
    end else begin
      vrf_en = stages[0].en;
      vrf_we = stages[0].we;
      vrf_addr = stages[0].addr;
    end
  end


  always_comb begin
    free = ~stages[0].en
      & ~stages[1].en
      & ~stages[MULT_STAGES].en;
  end

endmodule




/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
