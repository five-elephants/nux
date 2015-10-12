/** _use_m4_ macros
 * include(ops.m4)
 */

// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Fub_synapse
  #(parameter int NUM_LUTS = 2,
    parameter int REG_WIDTH = 128,
    parameter int REGS_PER_SET = 4)
  ( input logic clk, reset,
    
    input Frontend::Issue_slot inst,
    Operand_if.read opbus,

    Syn_io_if.client syn_io_a,
    Syn_io_if.client syn_io_b,
    output logic synapse_busy,
    output logic synapse_stall,

    output Backend::Result_bus resbus );

  import Pu_inst::*;
  import Pu_types::*;

  //---------------------------------------------------------------------------
  // Local types and signals
  //---------------------------------------------------------------------------

  localparam int NUM_NIBBLES = REG_WIDTH / 4;
  localparam int NUM_WORDS = REG_WIDTH / 32;
  localparam int AB_SELECT_BIT = 16;

  typedef logic[3:0] Nibble;
  typedef Nibble[0:15] Lookup_table;
  typedef logic[clog2(NUM_LUTS)-1:0] Lut_index;
  typedef logic[NUM_NIBBLES-1:0] Select_state;
  typedef logic[REG_WIDTH-1:0] Vector;
  typedef logic[clog2(REGS_PER_SET)-1:0] Vector_index;
  typedef logic[clog2(NUM_WORDS)-1:0] Vector_subindex;

  Lookup_table lut[0:NUM_LUTS-1];
  Vector svr[0:1][0:REGS_PER_SET-1];
  logic svr_switch;
  Syn_io::Eval_pattern[0:3] eval_patterns;

  Inst ir;
  Word aa, bb, cc;
  Vector map_res;
  Vector select_res;
  Lut_index next_lut_sel, lut_sel;
  Select_state next_select_state, select_state;
  logic next_save_select_state, save_select_state;
  logic next_write_pattern, write_pattern;
  logic next_output_pattern, output_pattern;
  logic next_output_mfvr, output_mfvr;
  logic next_output_map, output_map;
  logic next_output_mtvr, output_mtvr;
  logic next_output_mv, output_mv;
  logic next_save_lut, save_lut;
  Vector_index src_a;
  Vector v_aa, v_bb;
  logic compare_zero;

  Vector front_res;
  logic next_front_we, front_we;
  Vector_index next_front_dest, front_dest;

  logic swap;

  Vector_subindex next_mtvr_index, mtvr_index;
  Vector mtvr_res;
  Word mfvr_res;
  Vector mv_res;

  Word addr;
  Word seq;
  logic ab_select;
  logic next_start_seq, start_seq;
  logic seq_busy_a, seq_busy_b;
  Vector data_mask;

  logic pending_ops, next_pending_ops;
  logic pending_ops_d;
  Word pending_seq, next_pending_seq;
  Word pending_addr, next_pending_addr;

  //---------------------------------------------------------------------------
  // Decode
  //---------------------------------------------------------------------------
  
  assign ir = inst.ir;
  assign aa = opbus.opbus_0.a;
  assign bb = opbus.opbus_0.b;
  assign cc = opbus.opbus_0.c;

  assign addr = (pending_ops_d ? pending_addr : (aa + bb));
  assign ab_select = addr[AB_SELECT_BIT];
  assign seq = (pending_ops_d ? pending_seq : cc);

  always_comb begin
    // default assignment
    next_output_map = 1'b0;
    next_output_mtvr = 1'b0;
    next_output_mv = 1'b0;
    next_save_select_state = 1'b0;
    next_save_lut = 1'b0;
    next_lut_sel = '0;
    next_front_dest = ir.x.rt[$left(next_front_dest):$right(next_front_dest)];
    next_front_we = 1'b0;
    swap = 1'b0;
    next_mtvr_index = ir.x.rb[$left(next_mtvr_index):$right(next_mtvr_index)];
    src_a = ir.x.ra[$left(Vector_index):$right(Vector_index)];
    //next_start_seq = 1'b0;
    next_start_seq = pending_ops & !(seq_busy_a || seq_busy_b);
    next_write_pattern = 1'b0;
    next_output_pattern = 1'b0;
    next_output_mfvr = 1'b0;

    OPCMP(ir)
      OPNVE(Xop_synm): begin
        next_output_map = 1'b1;
        next_lut_sel = ir.x.rb;
        next_front_we = 1'b1;
      end

      OP(Op_syncmpi), OP(Op_syncmpi_rec):
        next_save_select_state = 1'b1;

      OPNVE(Xop_synmtl): begin
        next_save_lut = 1'b1;
        next_lut_sel = ir.x.rt;
      end

      OPNVE(Xop_synswp): begin
        swap = 1'b1;
      end

      OPNVE(Xop_synmtvr): begin
        next_front_we = 1'b1;
        next_output_mtvr = 1'b1;
        src_a = ir.x.rt[$left(Vector_index):$right(Vector_index)];
      end

      OPNVE(Xop_synmtp): begin
        next_write_pattern = 1'b1;
      end

      OPNVE(Xop_synmfp): begin
        next_output_pattern = 1'b1;
      end

      OPNVE(Xop_synmfvr): begin
        next_output_mfvr = 1'b1;
      end

      OPNVE(Xop_synmvvr): begin
        next_front_we = 1'b1;
        next_output_mv = 1'b1;
      end

      OPNVE(Xop_syns): begin
        next_front_we = 1'b1;
      end

      OPNVE(Xop_synops): begin
        next_start_seq = 1'b1;
      end

      default: begin end
    ENDOPCMP
  end 
  
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      lut_sel <= '0;
      output_map <= 1'b0;
      output_mtvr <= 1'b0;
      output_mv <= 1'b0;
      save_lut <= 1'b0;
      save_select_state <= 1'b0;
      front_dest <= '0;
      front_we <= 1'b0;
      mtvr_index <= '0;
      start_seq <= 1'b0;
      write_pattern <= 1'b0;
      output_pattern <= 1'b0;
      output_mfvr <= 1'b0;
    end else begin
      //if( inst.valid ) begin
        output_map <= next_output_map;
        output_mtvr <= next_output_mtvr;
        output_mv <= next_output_mv;
        save_lut <= next_save_lut;
        lut_sel <= next_lut_sel;
        save_select_state <= next_save_select_state;
        front_we <= next_front_we;
        front_dest <= next_front_dest;
        mtvr_index <= next_mtvr_index;
        start_seq <= next_start_seq;
        write_pattern <= next_write_pattern;
        output_pattern <= next_output_pattern;
        output_mfvr <= next_output_mfvr;
      //end
    end

  //---------------------------------------------------------------------------
  // vector register fetch
  //---------------------------------------------------------------------------

  always_ff @(posedge clk)
  begin
    if( front_we && (src_a == front_dest) )
      v_aa <= front_res;
    else
      v_aa <= svr[svr_switch][src_a];

    if( front_we && (ir.x.rb[$left(Vector_index):$right(Vector_index)] == front_dest) )
      v_bb <= front_res;
    else
      v_bb <= svr[svr_switch][ir.x.rb[$left(Vector_index):$right(Vector_index)]];
  end

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      svr_switch <= 1'b0;
    end else begin
      svr_switch <= svr_switch ^ swap;
    end

  //---------------------------------------------------------------------------
  // Datapath
  //---------------------------------------------------------------------------


  /** Lookup table register */
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      for(int i=0; i<NUM_NVE_LUT; i++)
        lut[i] <= '0;
    end else begin
      if( save_lut ) begin
        lut[lut_sel] <= {aa, bb};
      end
    end
 
  /** eval pattern register */
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      eval_patterns[0] <= 4'b1001;
      eval_patterns[1] <= 4'b0110;
      eval_patterns[2] <= 4'b0101;
      eval_patterns[3] <= 4'b1010;
    end else begin
      if( write_pattern ) begin
        {eval_patterns[0], eval_patterns[1], eval_patterns[2], eval_patterns[3]} <= aa[31:16];
      end
    end

  Never_map #(
    .WIDTH(REG_WIDTH)
  ) map (
    .lut(lut[lut_sel]),
    .a(v_aa),
    .res(map_res)
  );

  Never_select #(
    .WIDTH(REG_WIDTH)
  ) select (
    .sel(select_state),
    .a(v_aa),
    .b(v_bb),
    .res(select_res)
  );

  Never_compare #(
    .WIDTH(REG_WIDTH)
  ) compare (
    .a(v_aa),
    .pattern(bb[3:0]),
    .mask(bb[7:4]),
    .out_mask(next_select_state),
    .zero(compare_zero)
  );

  /** Internal selection state */
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      select_state <= '0;
    end else begin
      if( save_select_state )
        select_state <= next_select_state;
    end

  /** move to vector register */
  always_comb begin
    mtvr_res = v_aa;
    mtvr_res[REG_WIDTH - (mtvr_index * 32) -1 -: 32] = aa;
    mfvr_res = v_aa[REG_WIDTH - (mtvr_index * 32) -1 -: 32];
    mv_res = v_aa;
  end


  /** Output to result bus */
  always_comb begin
    resbus.valid = 1'b1;
    resbus.crf = '0;
    resbus.crf.eq = compare_zero;
    resbus.crf.gt = ~compare_zero;
    resbus.ov = 1'b0;
    resbus.cout = 1'b0;
    resbus.res_b = '0;
    resbus.msr = '0;
    
    unique case({output_mfvr, output_pattern})
      2'b10:  resbus.res_a = mfvr_res;
      2'b01:  resbus.res_a = {eval_patterns[0], eval_patterns[1], eval_patterns[2], eval_patterns[3]};
      default: resbus.res_a = 'x;
    endcase
  end

  always_comb 
    unique case({output_map, output_mtvr, output_mv})
      3'b100:   front_res = map_res;
      3'b010:   front_res = mtvr_res;
      3'b001:   front_res = mv_res;
      default:  front_res = select_res;
    endcase

  /** connection to synapse io controller */
  always_comb begin
    syn_io_a.client2syn_data = svr[~svr_switch][0];
    syn_io_a.client2syn_patterns = eval_patterns;
    syn_io_b.client2syn_data = svr[~svr_switch][0];
    syn_io_b.client2syn_patterns = eval_patterns;
  end

  assign synapse_busy = seq_busy_a | seq_busy_b 
    | start_seq | next_start_seq; 
  assign synapse_stall = pending_ops | next_pending_ops;

  Syn_io_seq syn_io_seq_a (
    .clk, .reset,
    .syn_io(syn_io_a),
    .start(start_seq & ~ab_select & ~(seq_busy_a | seq_busy_b)),
    .seq(seq),
    .addr(addr),
    .busy(seq_busy_a)
  );

  Syn_io_seq syn_io_seq_b (
    .clk, .reset,
    .syn_io(syn_io_b),
    .start(start_seq & ab_select & ~(seq_busy_a | seq_busy_b)),
    .seq(seq),
    .addr(addr),
    .busy(seq_busy_b)
  );

  //---------------------------------------------------------------------------
  // Backlog for synapse sequencer operations
  //---------------------------------------------------------------------------
 
  always_comb begin
    // default assignment
    next_pending_ops = pending_ops;
    next_pending_seq = pending_seq;
    next_pending_addr = pending_addr;

    if( (seq_busy_a || seq_busy_b) && start_seq ) begin
      next_pending_ops = 1'b1;
      next_pending_seq = cc;
      next_pending_addr = addr;
    end else if( pending_ops && !(seq_busy_a || seq_busy_b) ) begin
      next_pending_ops = 1'b0;
    end
  end

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      pending_ops <= 1'b0;
      pending_ops_d <= 1'b0;
      pending_seq <= '0;
      pending_addr <= '0;
    end else begin
      pending_ops <= next_pending_ops;
      pending_ops_d <= pending_ops;
      pending_seq <= next_pending_seq;
      pending_addr <= next_pending_addr;
    end

  //---------------------------------------------------------------------------
  // vector register write-back
  //---------------------------------------------------------------------------
 
  always_comb begin
    logic[0:3] tmp;

    tmp = '0;
    data_mask = 'x;

    if( syn_io_a.syn2client_valid ) begin
      tmp[syn_io_a.syn2client_pat_ctr] = 1'b1;
      data_mask = {32{tmp}};
    end else if( syn_io_b.syn2client_valid ) begin
      tmp[syn_io_b.syn2client_pat_ctr] = 1'b1;
      data_mask = {32{tmp}};
    end
  end

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
    end else begin
      logic[0:3] tmp;

      if( front_we )
        svr[svr_switch][front_dest] <= front_res;

      tmp = {syn_io_a.syn2client_valid, syn_io_b.syn2client_valid,
          syn_io_a.syn2client_channel, syn_io_b.syn2client_channel};
      unique casez(tmp)
        4'b1000:   svr[~svr_switch][0] <= syn_io_a.syn2client_data;
        4'b1010:   svr[~svr_switch][1] <= (syn_io_a.syn2client_data & data_mask) | svr[~svr_switch][1];
        4'b0100:   svr[~svr_switch][0] <= syn_io_b.syn2client_data;
        4'b0101:   svr[~svr_switch][1] <= (syn_io_a.syn2client_data & data_mask) | svr[~svr_switch][1];

        4'b00zz:   begin
        end

        default: begin
          svr[~svr_switch][0] <= 'x;
          svr[~svr_switch][1] <= 'x;
        end
      endcase

      //if( syn_io_a.syn2client_valid ) begin
        //if( syn_io_a.syn2client_channel == 1'b1 )
          //svr[~svr_switch][1] <= syn_io_a.syn2client_data;
        //else
          //svr[~svr_switch][0] <= syn_io_a.syn2client_data;
      //end else begin
        //if( syn_io_b.syn2client_valid )
          //if( syn_io_b.syn2client_channel == 1'b1 )
            //svr[~svr_switch][1] <= syn_io_b.syn2client_data;
          //else
            //svr[~svr_switch][0] <= syn_io_b.syn2client_data;
      //end
    end

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
