// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module Result_shiftreg
  #(parameter int DEST_SIZE = 5,
    parameter int SRC_SIZE = 3,
    parameter int NUM_STAGES = 3,
    parameter int NUM_TESTPORTS = 1,
    parameter bit DETECT_WAW = 1'b0,
    parameter int STAGE_TEST_LOW = 0,
    parameter int STAGE_PREOUT = 0 )
	(	input logic clk, reset,
    input logic shift,

    input logic[DEST_SIZE-1:0] dest,
    input logic[SRC_SIZE-1:0] src,
    input logic[NUM_STAGES-1:0] stage,
    input logic we,
    output logic occupied,
    output logic waw_hazard,

    input logic[DEST_SIZE-1:0] test[0:NUM_TESTPORTS-1],
    output logic found[0:NUM_TESTPORTS-1],
    output logic index[0:NUM_TESTPORTS-1][0:NUM_STAGES-1],

    output logic empty,

    output logic[DEST_SIZE-1:0] preout_dest,
    output logic[SRC_SIZE-1:0] preout_src,
    output logic preout_valid,

    output logic[DEST_SIZE-1:0] out_dest,
    output logic[SRC_SIZE-1:0] out_src,
    output logic out_valid );


//---------------------------------------------------------------------------
// Internal types and signals
//---------------------------------------------------------------------------

typedef logic[DEST_SIZE-1:0] Dest;
typedef logic[SRC_SIZE-1:0] Src;
typedef logic[NUM_STAGES-1:0] Stages;


typedef struct packed {
  logic valid;
  Dest dest;
  Src src;
} Shift_data;


Shift_data shreg[0:NUM_STAGES-1];


//---------------------------------------------------------------------------
// Shift register process
//---------------------------------------------------------------------------

/** Shift the shift register and insert new entries at stage indicated by
* stage. */
always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    for(int i=0; i<NUM_STAGES; i++) begin
      //shreg[i] <= '0;
      shreg[i].valid <= 1'b0;  // only clear valids
    end
  end else begin
    if( shift ) begin
      for(int i=0; i<NUM_STAGES-1; i++) begin
        if( we && stage[i] ) begin
          shreg[i].valid <= 1'b1;
          shreg[i].dest <= dest;
          shreg[i].src <= src;
        end else begin
          shreg[i] <= shreg[i+1];
        end
      end

      if( we && stage[NUM_STAGES-1] ) begin
        shreg[NUM_STAGES-1].valid <= 1'b1;
        shreg[NUM_STAGES-1].dest <= dest;
        shreg[NUM_STAGES-1].src <= src;
      end else begin
        shreg[NUM_STAGES-1] <= '0;
      end
    end
  end


//---------------------------------------------------------------------------
// Output
//---------------------------------------------------------------------------

assign
  out_valid = shreg[0].valid,
  out_dest = shreg[0].dest,
  out_src = shreg[0].src;

assign
  preout_valid = shreg[STAGE_PREOUT].valid,
  preout_dest = shreg[STAGE_PREOUT].dest,
  preout_src = shreg[STAGE_PREOUT].src;

always_comb begin
  empty = 1'b1;

  for(int i=0; i<NUM_STAGES; i++) 
    if( shreg[i].valid ) 
      empty = 1'b0;
end

//---------------------------------------------------------------------------
// Occupied check
//---------------------------------------------------------------------------

always_comb begin
  occupied = 1'b0;

  //if( we ) begin
    for(int i=0; i<NUM_STAGES-1; i++)
      if( shreg[i+1].valid & stage[i] )
        occupied = 1'b1;
  //end
end

//---------------------------------------------------------------------------
// Compare logic
//---------------------------------------------------------------------------

generate
  genvar tport;
  genvar stg;

  for(tport=0; tport<NUM_TESTPORTS; tport++) begin : gen_testport
    logic cmp[0:NUM_STAGES-1];

    for(stg=STAGE_TEST_LOW; stg<NUM_STAGES; stg++) begin : gen_stage_cmp
      assign cmp[stg] = (& (~(test[tport] ^ shreg[stg].dest)));
    end : gen_stage_cmp

    always_comb begin
      // default assignment
      found[tport] = 1'b0;
      for(int i=0; i<NUM_STAGES; i++)
        index[tport][i] = 1'b0;

      for(int i=STAGE_TEST_LOW; i<NUM_STAGES; i++)
        if( cmp[i] && shreg[i].valid ) begin
          found[tport] = 1'b1;
          index[tport][i] = 1'b1;
          break;
        end
    end

  end : gen_testport
endgenerate

//---------------------------------------------------------------------------
// Write-after-write hazard detection
//---------------------------------------------------------------------------

generate
if( DETECT_WAW == 1'b1 ) begin : gen_waw_detect
  /* Test wheter there is a write entry with the same dest for a stage higher
  * than indicated by the stage input. */

  logic[0:NUM_STAGES-1] cmp;
  logic[0:NUM_STAGES-1] mask;
  logic[0:NUM_STAGES-1] masked_cmp;

  /** Generate a temperature encoded mask */
  genvar mask_bit;
  for(mask_bit=1; mask_bit<NUM_STAGES; mask_bit++) begin : gen_mask
    assign mask[mask_bit] = (| stage[mask_bit-1:0]);
  end : gen_mask

  assign mask[0] = 1'b0;

  /** Generate a comparator for every stage to compare with the dest input. */
  genvar stg;
  for(stg=0; stg<NUM_STAGES; stg++) begin : gen_stage_cmp
    assign cmp[stg] = (& (~(dest ^ shreg[stg].dest))) & shreg[stg].valid;
  end : gen_stage_cmp
  
  /** A WAW hazard is detected, when one of the higher stages already has
  * a write to the current dest. */
  assign masked_cmp = cmp & mask;
  assign waw_hazard = (| masked_cmp);

end : gen_waw_detect
else
begin : gen_no_waw_detect
  assign waw_hazard = 1'b0;
end : gen_no_waw_detect

endgenerate


endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
