// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Inst_track
  #(parameter bit WRITE_THROUGH = 1'b1,
    parameter bit LOOKUP_CACHE = 1'b1 )
  ( input logic clk, reset,
    
    input Frontend::Fetch_state fst,
    input Frontend::Predecoded predec,
    
    input disable_wb,

    output logic ready,
    output logic pipe_empty,
    input logic issue,
    Wb_channel_if.ctrl wb_gpr,
    Wb_channel_if.ctrl wb_cr,
    Wb_channel_if.ctrl wb_ctr,
    Wb_channel_if.ctrl wb_lnk,
    Wb_channel_if.ctrl wb_xer,
    Wb_channel_if.ctrl wb_spr,
    Wb_channel_if.ctrl wb_msr,

    input Frontend::Delayed_commit del_commit );
    
import Frontend::*;
import Pu_types::*;


    //Delayed_wb_if.inst_track wbd_ls_gpr );

//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

localparam int shreg_stages = $bits(Inst_latency_onehot);
localparam int shreg_stages_short = 4;

Wb_channel_if wb_branch_dummy();
Wb_channel_if wb_mem_dummy();
Wb_channel_if wb_nve_dummy();

logic shift;
Reg_index ra, rb, rt;
logic ready_gpr;
logic ready_cr;
logic ready_ctr;
logic ready_lnk;
logic ready_xer;
logic ready_spr;
logic ready_msr;
//logic ready_ls_gpr_delayed;
logic empty_gpr;
logic empty_cr;
logic empty_ctr;
logic empty_lnk;
logic empty_xer;
logic empty_spr;
logic empty_branch;
logic empty_mem;
logic empty_nve;
logic empty_msr;

logic found_ls_gpr_delayed_w;
logic ready_ls_gpr_delayed_r[0:2];

logic schedule_wb;


assign shift = 1'b1;
assign
  ra = predec.ra,
  rb = predec.rb,
  rt = predec.rt;
assign schedule_wb = ~predec.nd_latency;

assign ready = ready_gpr 
  & ready_cr 
  & ready_ctr 
  & ready_lnk 
  & ready_xer
  & ready_spr
  & ready_msr;
  //& ready_ls_gpr_delayed;

assign pipe_empty = empty_gpr 
  & empty_cr 
  & empty_ctr 
  & empty_lnk 
  & empty_branch 
  & empty_xer
  & empty_spr
  & empty_mem
  //& empty_nve
  & empty_msr;

//---------------------------------------------------------------------------
// XXX instruction delay counter to force execution in program order.
// Alternatively implement this as a shift register.
// (Perhaps make it configurable whether this is used.)
//---------------------------------------------------------------------------


//---------------------------------------------------------------------------
// Result shift registers for write-back channels
//---------------------------------------------------------------------------

logic gpr_write;
Reg_index gpr_dest;
logic gpr_read[0:2];
Reg_index gpr_read_dest[0:2];

assign 
  gpr_read_dest[0] = predec.ra,
  gpr_read_dest[1] = predec.rb,
  gpr_read_dest[2] = predec.rt;
assign 
  gpr_read[0] = predec.read_ra,
  gpr_read[1] = predec.read_rb,
  gpr_read[2] = predec.read_rt;

assign gpr_write = (predec.write_ra | predec.write_rt);
assign gpr_dest = predec.write_ra ? predec.ra : predec.rt;

Track #(
  .DEST_SIZE($bits(Reg_index)),
  .NUM_TESTPORTS(3),
  .SHREG_STAGES(shreg_stages),
  .WRITE_THROUGH(WRITE_THROUGH),
  //.WRITE_THROUGH(1'b0),
  .USE_LOOKUP_CACHE(LOOKUP_CACHE)
) track_gpr (
  .write(gpr_write),
  .dest(gpr_dest),
  .read(gpr_read),
  .read_dest(gpr_read_dest),
  .ready(ready_gpr),
  .empty(empty_gpr),
  .wb(wb_gpr),
  .delayed_commit(del_commit.valid),
  .delayed_dest(del_commit.gpr),
  .predec(predec),
  .*
);

//---------------------------------------------------------------------------

generate
  wire [0:7] ready_crf;
  wire [0:7] empty_crf;
  wire [0:7] wb_crf_we;
  Fu_set wb_crf_src[0:7];

  //Wb_channel_if #(1) wb_crf [0:7] ();


  /** generate trackers for every CR field */
  genvar crf_i;
  for(crf_i=0; crf_i<8; crf_i++) begin : gen_crf_track
    logic cr_read[0:0];
    logic cr_read_dest[0:0];

    Wb_channel_if #(1) wb_crf();

    assign cr_read[0] = predec.read_cr_0[crf_i]
      | predec.read_cr_1[crf_i]
      | predec.read_cr_2[crf_i];

    assign cr_read_dest[0] = 1'b1;

    Track #(
      .DEST_SIZE(1),
      .NUM_TESTPORTS(1),
      .SHREG_STAGES(shreg_stages)
    ) track_crf (
      .write( (| predec.write_cr) ),
      .dest(predec.write_cr[crf_i]),
      .read(cr_read),
      .read_dest(cr_read_dest),
      .ready(ready_crf[crf_i]),
      .empty(empty_crf[crf_i]),
      //.wb(wb_crf[crf_i]),
      .wb(wb_crf.ctrl),
      .delayed_commit(1'b0),
      .delayed_dest('0),
      .predec(predec),
      .*
    );

    //assign wb_cr.dest[crf_i] = wb_crf[crf_i].dest;
    assign wb_cr.dest[crf_i] = wb_crf.dest;
    assign wb_crf_we[crf_i] = wb_crf.we;
    assign wb_crf_src[crf_i] = wb_crf.src;
  end : gen_crf_track

  assign ready_cr = (& ready_crf);
  assign empty_cr = (& empty_crf);

  /** control write back channel for CR */
  always_comb begin
    wb_cr.src = wb_crf_src[0];
    wb_cr.we = 
         wb_crf_we[0] | wb_crf_we[1] | wb_crf_we[2] | wb_crf_we[3]
       | wb_crf_we[4] | wb_crf_we[5] | wb_crf_we[6] | wb_crf_we[7];
  end

endgenerate

//---------------------------------------------------------------------------

logic ctr_read[0:0];
logic ctr_read_dest[0:0];

assign ctr_read_dest[0] = 1'b0;
assign ctr_read[0] = predec.read_ctr;

Track #(
  .DEST_SIZE(1),
  .NUM_TESTPORTS(1),
  .SHREG_STAGES(shreg_stages_short)
) track_ctr (
  .write(predec.write_ctr),
  .dest(1'b0),
  .read(ctr_read),
  .read_dest(ctr_read_dest),
  .ready(ready_ctr),
  .empty(empty_ctr),
  .wb(wb_ctr),
  .delayed_commit(1'b0),
  .delayed_dest('0),
  .predec(predec),
  .*
);

//---------------------------------------------------------------------------

logic lnk_read[0:0];
logic lnk_read_dest[0:0];

assign lnk_read_dest[0] = 1'b0;
assign lnk_read[0] = predec.read_lnk;

Track #(
  .DEST_SIZE(1),
  .NUM_TESTPORTS(1),
  .SHREG_STAGES(shreg_stages_short)
) track_lnk (
  .write(predec.write_lnk),
  .dest(1'b0),
  .read(lnk_read),
  .read_dest(lnk_read_dest),
  .ready(ready_lnk),
  .empty(empty_lnk),
  .wb(wb_lnk),
  .delayed_commit(1'b0),
  .delayed_dest('0),
  .predec(predec),
  .*
);

//---------------------------------------------------------------------------

logic xer_read[0:0];
logic[$bits(Xer_dest)-1:0] xer_read_dest[0:0];

assign xer_read_dest[0] = XER_DEST_ALL;
assign xer_read[0] = predec.read_xer;

Track #(
  .DEST_SIZE($bits(Xer_dest)),
  .NUM_TESTPORTS(1),
  .SHREG_STAGES(shreg_stages)
) track_xer (
  .write(predec.write_xer),
  .dest(predec.xer_dest),
  .read(xer_read),
  .read_dest(xer_read_dest),
  .ready(),
  .empty(empty_xer),
  .wb(wb_xer),
  .delayed_commit(1'b0),
  .delayed_dest({$bits(Xer_dest){1'b0}}),
  .predec(predec),
  .*
);

assign ready_xer = empty_xer;

//---------------------------------------------------------------------------

logic branch_read[0:0];
logic branch_read_dest[0:0];

assign branch_read[0] = 1'b0;
assign branch_read_dest[0] = 1'b0;

Track #(
  .DEST_SIZE(1),
  .NUM_TESTPORTS(1),
  .SHREG_STAGES(shreg_stages_short)
) track_branch (
  .write(predec.is_branch),
  .dest(1'b0),
  .read(branch_read),
  .read_dest(branch_read_dest),
  .ready(),
  .empty(empty_branch),
  .wb(wb_branch_dummy.ctrl),
  .delayed_commit(1'b0),
  .delayed_dest('0),
  .predec(predec),
  .*
);

//---------------------------------------------------------------------------

logic spr_read[0:1];
logic[$bits(Spr_reduced)-1:0] spr_read_dest[0:1];

assign 
  spr_read[0] = predec.read_spr,
  spr_read[1] = predec.read_spr2;

assign
  spr_read_dest[0] = predec.spr,
  spr_read_dest[1] = predec.spr2;

Track #(
  .DEST_SIZE($bits(Spr_reduced)),
  //.DEST_SIZE(10),
  .NUM_TESTPORTS(2),
  .SHREG_STAGES(shreg_stages_short)
  //.USE_LOOKUP_CACHE(1'b0)
) track_spr (
  .write(predec.write_spr),
  .dest(predec.spr_dest),
  .read(spr_read),
  .read_dest(spr_read_dest),
  .ready(ready_spr),
  .empty(empty_spr),
  .wb(wb_spr),
  .delayed_commit(1'b0),
  .delayed_dest({$bits(Spr_reduced){1'b0}}),
  .predec(predec),
  .*
);

//---------------------------------------------------------------------------

logic mem_read[0:0];
logic[0:0] mem_read_dest[0:0];

assign mem_read[0] = 1'b0;
assign mem_read_dest[0] = 1'b1;

// XXX I think this is only needed for the MEM_TIGHT case
Track #(
  .DEST_SIZE(1),
  .NUM_TESTPORTS(1),
  .SHREG_STAGES(shreg_stages_short),
  .USE_LOOKUP_CACHE(LOOKUP_CACHE)
) track_mem (
  .write(predec.write_mem),
  .dest(1'b1),
  .read(mem_read),
  .read_dest(mem_read_dest),
  .ready(),
  .empty(empty_mem),
  .wb(wb_mem_dummy.ctrl),
  .delayed_commit(1'b0),
  .delayed_dest('0),
  .predec(predec),
  .*
);

//---------------------------------------------------------------------------

/*logic nve_read[0:0];
logic[0:0] nve_read_dest[0:0];

assign nve_read[0] = 1'b0;
assign nve_read_dest[0] = 1'b1;

Track #(
  .DEST_SIZE(1),
  .NUM_TESTPORTS(1),
  .SHREG_STAGES(shreg_stages_short),
  .USE_LOOKUP_CACHE(1'b1)
) track_nve (
  .write(predec.write_nve),
  .dest(1'b1),
  .read(nve_read),
  .read_dest(nve_read_dest),
  .ready(),
  .empty(empty_nve),
  .wb(wb_nve_dummy.ctrl),
  .delayed_commit(1'b0),
  .delayed_dest('0),
  .*
);*/


//---------------------------------------------------------------------------

logic msr_read[0:0];
logic msr_read_dest[0:0];

assign msr_read_dest[0] = 1'b0;
assign msr_read[0] = predec.read_msr;

Track #(
  .DEST_SIZE(1),
  .NUM_TESTPORTS(1),
  .SHREG_STAGES(shreg_stages_short)
) track_msr (
  .write(predec.write_msr),
  .dest(1'b0),
  .read(msr_read),
  .read_dest(msr_read_dest),
  .ready(ready_msr),
  .empty(empty_msr),
  .wb(wb_msr),
  .delayed_commit(1'b0),
  .delayed_dest('0),
  .predec(predec),
  .*
);

//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Delayed WB feature: Hold writes referring to a register in delayed
// write-back.
//---------------------------------------------------------------------------

/*Lookup_cache #(.SIZE(32)) ls_gpr_delayed_write_test_write (
  .clk, .reset,
  .set_addr(wbd_ls_gpr.track_dest),
  .set(wbd_ls_gpr.track_valid),
  .clear_addr(wbd_ls_gpr.wb_dest),
  .clear(wbd_ls_gpr.wb_ack & wbd_ls_gpr.wb_req),
  .test_addr(gpr_dest),
  .found(found_ls_gpr_delayed_w)
);*/

//assign ready_ls_gpr_delayed = (~(found_ls_gpr_delayed_w & gpr_write));

endmodule


//---------------------------------------------------------------------------
// Submodule
//---------------------------------------------------------------------------

module Track
  #( parameter int DEST_SIZE = 5,
     parameter int NUM_TESTPORTS = 3,
     parameter int SHREG_STAGES = 3,
     parameter bit WRITE_THROUGH = 1'b0,
     parameter bit USE_LOOKUP_CACHE = 1'b0 )
  ( input logic clk, reset,
    input logic write,
    input logic schedule_wb,
    input logic[DEST_SIZE-1:0] dest,
    input logic[DEST_SIZE-1:0] read_dest[0:NUM_TESTPORTS-1],
    input logic read[0:NUM_TESTPORTS-1],
    input Frontend::Predecoded predec,
    input logic issue,
    input logic shift,
    input logic disable_wb,
    output logic ready,
    output logic empty,
    Wb_channel_if.ctrl wb,
    input logic delayed_commit,
    input logic[DEST_SIZE-1:0] delayed_dest );


  localparam int NUM_SHR_TESTPORTS = USE_LOOKUP_CACHE ? 0 : NUM_TESTPORTS;
  localparam bit SHR_DETECT_WAW = !USE_LOOKUP_CACHE;
  localparam int SHR_STAGE_TEST_LOW = WRITE_THROUGH ? 2 : 1;
  //localparam int SHR_STAGE_TEST_LOW = WRITE_THROUGH ? 1 : 0;  // XXX latency performance bug
  localparam int SHR_STAGE_PREOUT = WRITE_THROUGH ? 1 : 0;
  localparam int LC_NUM_CLEAR_PORTS = 2;

  typedef logic[SHREG_STAGES-1:0] Latency_onehot;

  import Frontend::*;

  //---------------------------------------------------------------------------
  function automatic Latency_onehot latency_onehot(input Inst_latency lat);
    Latency_onehot rv;

    rv = '0;

    if( lat < SHREG_STAGES )
      rv[lat] = 1'b1;

    return rv;
  endfunction
  //---------------------------------------------------------------------------

  typedef logic[DEST_SIZE-1:0] Dest;

  Fu_set src;
  logic occupied;
  logic lc_waw_hazard;
  logic shr_waw_hazard;
  Dest test[0:NUM_SHR_TESTPORTS-1];
  logic found[0:NUM_SHR_TESTPORTS-1];
  logic index[0:NUM_SHR_TESTPORTS-1][0:SHREG_STAGES-1];
  logic not_ready;
  Dest out_dest;
  logic[$bits(Fu_set)-1:0] out_src_bits;
  Fu_set out_src;
  logic out_valid;
  Latency_onehot stage;
  logic should_insert;
  logic we;
  logic shr_empty, lc_empty;
  Dest preout_dest;
  logic preout_valid;

  assign
    src = predec.fu_set,
    stage = latency_onehot(predec.latency),
    should_insert = write;

  Result_shiftreg
    #(  .DEST_SIZE(DEST_SIZE),
        .SRC_SIZE($bits(Fu_set)),
        .NUM_STAGES(SHREG_STAGES),
        .NUM_TESTPORTS(NUM_SHR_TESTPORTS),
        .DETECT_WAW(!USE_LOOKUP_CACHE),
        .STAGE_TEST_LOW(SHR_STAGE_TEST_LOW),
        .STAGE_PREOUT(SHR_STAGE_PREOUT)
      ) res_shiftreg (
        .clk,
        .reset,
        .shift(1'b1),

        // insert new commands
        .dest(dest),
        .src(src),
        .stage(stage),
        .we(we & schedule_wb),
        .occupied(occupied),
        .waw_hazard(shr_waw_hazard),

        // check for writes in progress
        .test,
        .found,
        .index,

        .empty(shr_empty),

        // preout to invalidate lookup cache
        .preout_dest,
        .preout_src(),
        .preout_valid,

        // output at last stage to control write-back
        .out_dest,
        .out_src(out_src_bits),
        .out_valid
      );

  assign we = issue & should_insert & ~occupied;
  assign out_src = Fu_set'(out_src_bits);


  assign
    wb.we = out_valid & ~disable_wb,
    wb.dest = out_dest,
    wb.src = out_src;

  assign ready = ~not_ready;

  generate
  if( USE_LOOKUP_CACHE ) begin : gen_lookup_cache
    logic lc_found[0:NUM_TESTPORTS-1];
    logic[0:NUM_TESTPORTS-1] lc_found_and_read;
    logic lc_clear[0:LC_NUM_CLEAR_PORTS-1];
    Dest lc_clear_dest[0:LC_NUM_CLEAR_PORTS-1];


    /** Determine what to clear in the lookup-cache. */
    always_comb begin
      lc_clear[0] = delayed_commit;
      lc_clear[1] = preout_valid;

      lc_clear_dest[0] = delayed_dest;
      lc_clear_dest[1] = preout_dest;
    end

    Lookup_cache #(
      .SIZE(2**DEST_SIZE),
      .WRITE_THROUGH(WRITE_THROUGH),
      .NUM_CLEAR_PORTS(LC_NUM_CLEAR_PORTS)
    ) lookup_waw (
      .clk,
      .reset,
      .set_addr(dest),
      .set(we),
      .clear_addr(lc_clear_dest),
      .clear(lc_clear),
      .test_addr(dest),
      .found(lc_waw_hazard),
      .empty(lc_empty)
    );

    genvar port;
    for(port=0; port<NUM_TESTPORTS; port++) begin : gen_port
      
      Lookup_cache #(
        .SIZE(2**DEST_SIZE),
        .WRITE_THROUGH(WRITE_THROUGH),
        .NUM_CLEAR_PORTS(LC_NUM_CLEAR_PORTS)
      ) lookup (
        .clk,
        .reset,
        .set_addr(dest),
        .set(we),
        .clear_addr(lc_clear_dest),
        .clear(lc_clear),
        .test_addr(read_dest[port]),
        .found(lc_found[port]),
        .empty()  // only need to test emptiness on one cache (identical input)
      );

      assign lc_found_and_read[port] = lc_found[port] & read[port];

    end : gen_port

    // reduce results
    always_comb begin
      not_ready = (should_insert & (occupied | lc_waw_hazard)) | (|lc_found_and_read);
      empty = shr_empty & lc_empty;
    end

  end : gen_lookup_cache
  else
  begin : no_lookup_cache
    
    assign test = read_dest;

    always_comb begin
      empty = shr_empty;

      not_ready = should_insert & (occupied | shr_waw_hazard);
      for(int i=0; i<NUM_TESTPORTS; i++)
        not_ready = not_ready | (found[i] & read[i]);
    end

    `ifndef SYNTHESIS
    check_delayed_commit_requires_lookup_cache: assert property(
      @(posedge clk) disable iff(reset)
      ( delayed_commit == 1'b0 )
    );
    `endif /** SYNTHESIS */
    
  end : no_lookup_cache
  endgenerate

endmodule



// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
