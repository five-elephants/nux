// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_ctrl
  #(parameter int NUM_SLICES = 1,
    parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int VRF_SIZE = 32,
    parameter int SCALAR_SIZE = 32,
    parameter int MULT_STAGES = 1,
    parameter int ADD_STAGES = 1,
    parameter int MAX_IN_FLIGHT = 5,
    parameter int STALL_ON_FULL_LATENCY = 2)
  ( input logic clk, reset,
    input Frontend::Issue_slot inst,
    input Pu_types::Word a, b,
    output logic ready,
    output logic pipe_empty,

    Vector_slice_ctrl_if.ctrl slice_ctrl,
    Valu_ctrl_if.ctrl valu_ctrl,
    Vector_ls_ctrl_if.ctrl vls_ctrl,
    Vector_cmp_ctrl_if.ctrl cmp_ctrl,
    Vector_pls_ctrl_if.ctrl pls_ctrl,
    Vector_permute_ctrl_if.ctrl permute_ctrl);

  import Vector::*;


  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------

  typedef struct {
    logic valid;
    Rs_ref rs_ref;
  } Vrf_src_entry;

  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------

  Vrf_src_entry vrf_src[0:VRF_SIZE-1];
  Readlock_ctr vrf_readlock[0:VRF_SIZE-1];
  logic vcr_valid;
  Readlock_ctr vcr_readlock;

  Pu_inst::Inst ir, ir_d;
  logic inst_valid_d;
  logic q_push;
  logic q_pop, q_pop_d;
  Vector_operation q_op_in;
  logic q_empty;
  logic q_almost_full;
  logic q_full;
  Vector_operation q_op_out;
  logic read_rt;
  logic read_ra;
  logic read_rb;
  logic write_rt;
  logic read_vcr;
  logic write_vcr;
  logic issue;
  // signals for functional units
  //  VALU
  logic valu_valid;
  Pu_inst::Fxv_opcd valu_xo;
  Pu_inst::Fxv_cond valu_cond;
  Pu_types::Word valu_g;
  logic valu_result_avail;
  //  VLS
  logic vls_valid;
  Pu_inst::Fxv_opcd vls_xo;
  logic vls_result_avail;
  Pu_types::Word vls_g;
  //  CMP
  logic cmp_valid;
  Pu_inst::Fxv_opcd cmp_xo;
  logic cmp_result_avail;
  Pu_types::Word cmp_g;
  logic wb_vcr;
  //  PLS
  logic pls_valid;
  Pu_inst::Fxv_opcd pls_xo;
  Pu_inst::Fxv_cond pls_cond;
  logic pls_result_avail;
  Pu_types::Word pls_g;
  logic pls_stall;
  //  permute
  logic permute_valid;
  Pu_inst::Fxv_opcd permute_xo;
  logic permute_result_avail;
  logic permute_stall;
  Pu_types::Word permute_g;
  Vector::Permute_size permute_size;
  logic[4:0] permute_shift;

  // signals for reservation stations
  logic rs_full[0:NUM_UNITS-1];
  logic rs_empty[0:NUM_UNITS-1];
  Unit_id unit;
  Vector::Operands operands, operands_d;
  logic unit_readies[0:NUM_UNITS-1];
  logic unit_inserts[0:NUM_UNITS-1];
  Rs_ref insert_refs[0:NUM_UNITS-1];
  logic vrf_reqs[0:NUM_UNITS-1];
  logic vrf_reqs_or_reduced;
  logic vrf_req_mask[0:NUM_UNITS-1];
  logic vrf_acks[0:NUM_UNITS-1];
  Vrf_index vrf_addrs[0:NUM_UNITS-1];
  logic vrf_ens[0:NUM_UNITS-1];
  logic vrf_wes[0:NUM_UNITS-1];
  Rs_ref vrf_refs[0:NUM_UNITS-1];
  Vrf_index vrf_wb_addr, vrf_wb_addr_d;
  logic vrf_wb_en, vrf_wb_en_d;
  logic vrf_wb_we, vrf_wb_we_d;
  Rs_ref vrf_wb_ref;
  Unit vrf_src_unit;
  logic valu_stall;
  logic readlock_full;
  logic waw_hazard;
  logic war_hazard;
  logic vcr_waw_hazard;
  logic vcr_war_hazard;
  logic vcr_readlock_full;
  Readlock_ctr next_vrf_readlock_0;
  Readlock_ctr next_vrf_readlock_1;
  Readlock_ctr next_vrf_readlock_2;
  logic vcr_read_by_fus[0:NUM_UNITS-1];
  logic[$clog2(NUM_UNITS)-1:0] vcr_read_by_fus_reduced;


  //--------------------------------------------------------------------------------
  // Instruction handling
  //--------------------------------------------------------------------------------

  assign ir = inst.ir;
  assign ready = ~q_almost_full & ~q_full;
  assign pipe_empty = ~inst_valid_d
      & q_empty
      & rs_empty[VU_ID_MADD]
      & rs_empty[VU_ID_CMP]
      & rs_empty[VU_ID_LS]
      & rs_empty[VU_ID_PLS]
      & rs_empty[VU_ID_PERMUTE];


  //--------------------------------------------------------------------------------
  // Instruction producer
  //--------------------------------------------------------------------------------

  always_ff @(posedge clk) begin
    ir_d <= ir;
    inst_valid_d <= inst.valid;
  end

  always_comb begin : decode_and_insert
    // default assignments
    q_push = 1'b0;
    q_op_in = '0;
    q_op_in.rt = ir_d.fxv.rt;
    q_op_in.ra = ir_d.fxv.ra;
    q_op_in.rb = ir_d.fxv.rb;
    q_op_in.xo = ir_d.fxv.xo;
    q_op_in.cond = ir_d.fxv.cond;

    unique case(ir_d.fxv.xo)
      Pu_inst::Xop_fxvlax, Pu_inst::Xop_fxvstax,
      Pu_inst::Xop_fxvinx, Pu_inst::Xop_fxvoutx: begin
        q_op_in.g = a + b;
      end

      default: begin
        q_op_in.g = a;
      end
    endcase

    if( !q_full && inst_valid_d ) begin
      q_push = 1'b1;
    end
  end

  DW_fifo_s1_sf #(
    .width($bits(Vector_operation)),
    .depth(MAX_IN_FLIGHT),
    .ae_level(1),
    .af_level(STALL_ON_FULL_LATENCY),
    .err_mode(0),
    .rst_mode(2)   // async reset without FIFO memory
  ) op_queue (
    .clk(clk),
    .rst_n(~reset),
    .push_req_n(~q_push),
    .pop_req_n(~q_pop),
    .diag_n(1'b1),
    .data_in(q_op_in),
    .empty(q_empty),
    .almost_empty(),
    .half_full(),
    .almost_full(q_almost_full),
    .full(q_full),
    .error(),
    .data_out(q_op_out)
  );

  //--------------------------------------------------------------------------------
  // Instruction consumer
  //--------------------------------------------------------------------------------

  always_comb begin : decode_ops
    // default assignments
    read_ra = 1'b0;
    read_rb = 1'b0;
    read_rt = 1'b0;
    write_rt = 1'b0;
    unit = VU_ID_MADD;
    write_vcr = 1'b0;
    read_vcr = 1'b0;

    if( q_op_out.cond != Pu_inst::Fxv_cond_null )
      read_vcr = 1'b1;

    unique case(q_op_out.xo)
      Pu_inst::Xop_fxvmtach, Pu_inst::Xop_fxvmtachf,
      Pu_inst::Xop_fxvmtacb, Pu_inst::Xop_fxvmtacbf: begin
        read_ra = 1'b1;
        unit = VU_ID_MADD;
      end

      Pu_inst::Xop_fxvmahm, Pu_inst::Xop_fxvmahfs,
      Pu_inst::Xop_fxvaddhm, Pu_inst::Xop_fxvaddhfs,
      Pu_inst::Xop_fxvsubhm, Pu_inst::Xop_fxvsubhfs,
      Pu_inst::Xop_fxvmulhm, Pu_inst::Xop_fxvmulhfs,
      Pu_inst::Xop_fxvmabm, Pu_inst::Xop_fxvmabfs,
      Pu_inst::Xop_fxvmulbm, Pu_inst::Xop_fxvmulbfs,
      Pu_inst::Xop_fxvsubbm, Pu_inst::Xop_fxvsubbfs,
      Pu_inst::Xop_fxvaddbm, Pu_inst::Xop_fxvaddbfs:
      begin
        read_ra = 1'b1;
        read_rb = 1'b1;
        write_rt = 1'b1;
        unit = VU_ID_MADD;
      end

      Pu_inst::Xop_fxvmatachm, Pu_inst::Xop_fxvmatachfs,
      Pu_inst::Xop_fxvmultachm, Pu_inst::Xop_fxvmultachfs,
      Pu_inst::Xop_fxvaddtachm,
      Pu_inst::Xop_fxvmatacbm, Pu_inst::Xop_fxvmatacbfs,
      Pu_inst::Xop_fxvmultacbm, Pu_inst::Xop_fxvmultacbfs,
      Pu_inst::Xop_fxvaddtacb: begin
        read_ra = 1'b1;
        read_rb = 1'b1;
        write_rt = 1'b0;
        unit = VU_ID_MADD;
      end

      Pu_inst::Xop_fxvaddachm, Pu_inst::Xop_fxvaddachfs,
      Pu_inst::Xop_fxvaddacbm, Pu_inst::Xop_fxvaddacbfs: begin
        read_ra = 1'b1;
        write_rt = 1'b1;
        unit = VU_ID_MADD;
      end

      Pu_inst::Xop_fxvaddactachm, Pu_inst::Xop_fxvaddactachf,
      Pu_inst::Xop_fxvaddactacb, Pu_inst::Xop_fxvaddactacbf: begin
        read_ra = 1'b1;
        unit = VU_ID_MADD;
      end

      Pu_inst::Xop_fxvlax: begin
        read_rt = 1'b0;
        read_ra = 1'b0;
        read_rb = 1'b0;
        write_rt = 1'b1;
        unit = VU_ID_LS;
        read_vcr = 1'b0;
      end

      Pu_inst::Xop_fxvstax: begin
        read_rt = 1'b1;
        read_ra = 1'b0;
        read_rb = 1'b0;
        write_rt = 1'b0;
        unit = VU_ID_LS;
        read_vcr = 1'b0;
      end

      Pu_inst::Xop_fxvcmph,
      Pu_inst::Xop_fxvcmpb: begin
        read_rt = 1'b0;
        read_ra = 1'b1;
        read_rb = 1'b0;
        write_rt = 1'b0;
        unit = VU_ID_CMP;
        write_vcr = 1'b1;
        read_vcr = 1'b0;
      end

      Pu_inst::Xop_fxvinx: begin
        write_rt = 1'b1;
        //read_vcr = 1'b1;
        unit = VU_ID_PLS;
      end

      Pu_inst::Xop_fxvoutx: begin
        read_rt = 1'b1;
        //read_vcr = 1'b1;
        unit = VU_ID_PLS;
      end

      Pu_inst::Xop_fxvpckbl, Pu_inst::Xop_fxvpckbu, Pu_inst::Xop_fxvupckbl,
      Pu_inst::Xop_fxvupckbr: begin
        read_vcr = 1'b0;
        read_ra = 1'b1;
        read_rb = 1'b1;
        write_rt = 1'b1;
        unit = VU_ID_PERMUTE;
      end

      Pu_inst::Xop_fxvsel: begin
        //read_vcr = 1'b1;
        read_ra = 1'b1;
        read_rb = 1'b1;
        write_rt = 1'b1;
        unit = VU_ID_PERMUTE;
      end

      Pu_inst::Xop_fxvsplath,
      Pu_inst::Xop_fxvsplatb: begin
        read_vcr = 1'b0;
        write_rt = 1'b1;
        unit = VU_ID_PERMUTE;
      end

      Pu_inst::Xop_fxvshh,
      Pu_inst::Xop_fxvshb: begin
        read_vcr = 1'b0;
        write_rt = 1'b1;
        read_ra = 1'b1;
        unit = VU_ID_PERMUTE;
      end

      default: begin
      end
    endcase
  end


  always_comb begin
    operands.require_vcr = read_vcr;
    operands.vcr_valid = vcr_valid | wb_vcr;
    operands.g = q_op_out.g;
    operands.dest = q_op_out.rt;
    if( read_rt ) begin
      operands.src[0] = q_op_out.rt;
      operands.required[0] = read_rt;
      operands.valid[0] = ~vrf_src[q_op_out.rt].valid;
      operands.src_ref[0] = vrf_src[q_op_out.rt].rs_ref;
    end else begin
      operands.src[0] = q_op_out.ra;
      operands.required[0] = read_ra;
      operands.valid[0] = ~vrf_src[q_op_out.ra].valid;
      operands.src_ref[0] = vrf_src[q_op_out.ra].rs_ref;
    end

    operands.src[1] = q_op_out.rb;
    operands.required[1] = read_rb;
    operands.write_dest = write_rt;
    operands.valid[1] = ~vrf_src[q_op_out.rb].valid;
    operands.src_ref[1] = vrf_src[q_op_out.rb].rs_ref;

    // check for ongoing write-back to dependency
    if( vrf_wb_en && vrf_wb_we && (vrf_wb_ref == operands.src_ref[0]) )
      operands.valid[0] = 1'b1;
    if( vrf_wb_en && vrf_wb_we && (vrf_wb_ref == operands.src_ref[1]) )
      operands.valid[1] = 1'b1;

    // check to prevent overflow of readlock counter
    if( (vrf_readlock[q_op_out.ra] > unsigned'(READLOCK_MAX - 6))
        || (vrf_readlock[q_op_out.rb] > unsigned'(READLOCK_MAX - 6)) )
      readlock_full = 1'b1;
    else
      readlock_full = 1'b0;

    if( vcr_readlock > READLOCK_MAX )
      vcr_readlock_full = 1'b1;
    else
      vcr_readlock_full = 1'b0;

    // check additional hazards
    waw_hazard = vrf_src[q_op_out.rt].valid & write_rt;  // TODO wait in reservation station
    //war_hazard = (vrf_readlock[q_op_out.rt] > 0) & write_rt;  // TODO wait in reservation station
    war_hazard = ((vrf_readlock[q_op_out.rt] > 0)
        | (q_pop_d &
          ((operands_d.required[0] & (q_op_out.rt == operands_d.src[0])) 
          | (operands_d.required[1] & (q_op_out.rt == operands_d.src[1]))))) & write_rt;  // TODO wait in reservation station
    vcr_waw_hazard = ~vcr_valid & write_vcr;
    vcr_war_hazard = (vcr_readlock > 0) & write_vcr;
  end


  always_comb begin : consume_and_issue
    // default assignments
    q_pop = 1'b0;
    for(int i=$left(unit_inserts); i<=$right(unit_inserts); i++)
      unit_inserts[i] = 1'b0;

    if( !q_empty ) begin
      if( !rs_full[unit]
          && !readlock_full
          && !waw_hazard
          && !war_hazard
          && !vcr_readlock_full
          && !vcr_waw_hazard
          && !vcr_war_hazard )
      begin
        q_pop = 1'b1;
        unit_inserts[unit] = 1'b1;
      end
    end
  end


  // track source reservation stations for VRF
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      for(int i=0; i<VRF_SIZE; i++) begin
        vrf_src[i].valid <= 1'b0;
      end
    end else begin
      if( q_pop && operands.write_dest ) begin
        vrf_src[operands.dest].valid <= 1'b1;
        vrf_src[operands.dest].rs_ref <= insert_refs[unit];
      end

      if( vrf_wb_en && vrf_wb_we ) begin
        vrf_src[vrf_wb_addr].valid <= 1'b0;
      end
    end


  //--------------------------------------------------------------------------------
  // track reads on VRF registers
  //--------------------------------------------------------------------------------

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      //{>>{operands_d}} <= {$bits(operands_d){1'b0}};
      q_pop_d <= 1'b0;
      vrf_wb_addr_d <= '0;
      vrf_wb_en_d <= 1'b0;
      vrf_wb_we_d <= 1'b0;
    end else begin
      operands_d <= operands;
      q_pop_d <= q_pop;
      vrf_wb_addr_d <= vrf_wb_addr;
      vrf_wb_en_d <= vrf_wb_en;
      vrf_wb_we_d <= vrf_wb_we;
    end

  always_comb begin
    // default assignments
    next_vrf_readlock_0 = vrf_readlock[operands_d.src[0]];
    next_vrf_readlock_1 = vrf_readlock[operands_d.src[1]];
    next_vrf_readlock_2 = vrf_readlock[vrf_wb_addr_d];

    if( q_pop_d && operands_d.required[0] )
      next_vrf_readlock_0 = next_vrf_readlock_0 + 1;

    if( q_pop_d && operands_d.required[1] ) begin
      if( operands_d.src[1] == operands_d.src[0] )
        next_vrf_readlock_1 = next_vrf_readlock_0 + 1;
      else
        next_vrf_readlock_1 = next_vrf_readlock_1 + 1;
    end else begin
      if( operands_d.src[1] == operands_d.src[0] )
        next_vrf_readlock_1 = next_vrf_readlock_0;
    end

    if( vrf_wb_en_d && !vrf_wb_we_d ) begin
      if( vrf_wb_addr_d == operands_d.src[1] )
        next_vrf_readlock_2 = next_vrf_readlock_1 - 1;
      else if( vrf_wb_addr_d == operands_d.src[0] )
        next_vrf_readlock_2 = next_vrf_readlock_0 - 1;
      else
        next_vrf_readlock_2 = next_vrf_readlock_2 - 1;
    end else begin
      if( vrf_wb_addr_d == operands_d.src[1] )
        next_vrf_readlock_2 = next_vrf_readlock_1;
      else if( vrf_wb_addr_d == operands_d.src[0] )
        next_vrf_readlock_2 = next_vrf_readlock_0;
    end
  end

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      for(int i=0; i<VRF_SIZE; i++) begin
        vrf_readlock[i] <= 0;
      end
    end else begin
      vrf_readlock[operands_d.src[0]] <= next_vrf_readlock_0;
      vrf_readlock[operands_d.src[1]] <= next_vrf_readlock_1;
      vrf_readlock[vrf_wb_addr_d] <= next_vrf_readlock_2;
    end


  //--------------------------------------------------------------------------------
  // Track writes to VCR
  //--------------------------------------------------------------------------------

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      vcr_valid <= 1'b1;
    end else begin
      if( q_pop && write_vcr )
        vcr_valid <= 1'b0;
      else if( wb_vcr )
        vcr_valid <= 1'b1;
    end


  //--------------------------------------------------------------------------------
  // Track reads to VCR
  //--------------------------------------------------------------------------------

  always_comb begin
    vcr_read_by_fus_reduced = 0;

    for(int i=0; i<NUM_UNITS; i++)
      if( vcr_read_by_fus[i] )
        vcr_read_by_fus_reduced = vcr_read_by_fus_reduced + 1;
  end

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      vcr_readlock <= 0;
    end else begin
      if( q_pop && read_vcr )
        vcr_readlock <= vcr_readlock + 1 - vcr_read_by_fus_reduced;
      else if( !(q_pop && read_vcr) )
        vcr_readlock <= vcr_readlock - vcr_read_by_fus_reduced;
    end


  //--------------------------------------------------------------------------------
  // Reservation stations
  //--------------------------------------------------------------------------------

  Vector_reservation_station #(
    .NUM_ENTRIES(4),
    //.NUM_ENTRIES(16),
    .NUM_OPERANDS(2),
    .CONTROL_WIDTH($bits(Pu_inst::Fxv_opcd) + $bits(Pu_inst::Fxv_cond)),
    .THIS_UNIT_ID(VU_ID_MADD)
  ) rs_madd (
    .clk,
    .reset,
    // insertion of new instructions
    .empty(rs_empty[VU_ID_MADD]),
    .full(rs_full[VU_ID_MADD]),
    .ready(unit_readies[VU_ID_MADD]),
    .insert(unit_inserts[VU_ID_MADD]),
    .control_in({q_op_out.xo, q_op_out.cond}),
    .operands(operands),
    .insert_ref(insert_refs[VU_ID_MADD]),
    // requesting access to VRF
    .vrf_req(vrf_reqs[VU_ID_MADD]),
    .vrf_ack(vrf_acks[VU_ID_MADD]),
    // control info for VRF
    .vrf_addr(vrf_addrs[VU_ID_MADD]),
    .vrf_en(vrf_ens[VU_ID_MADD]),
    .vrf_we(vrf_wes[VU_ID_MADD]),
    .vrf_ref(vrf_refs[VU_ID_MADD]),
    // monitor on result bus
    .vrf_wb_en(vrf_wb_en),
    .vrf_wb_we(vrf_wb_we),
    .vrf_wb_addr(vrf_wb_addr),
    .vrf_wb_ref(vrf_wb_ref),
    // VCR read access
    .vcr_read(vcr_read_by_fus[VU_ID_MADD]),
    .wb_vcr(wb_vcr),
    // enable operand input register during operand fetch
    .reg_in_en(slice_ctrl.valu_reg_in_en),
    // passing on operations to the datapath control logic
    .control_out({valu_xo, valu_cond}),
    .control_valid(valu_valid),
    .g(valu_g),
    .result_avail(valu_result_avail),
    .stall(valu_stall)
  );


  Vector_reservation_station #(
    .NUM_ENTRIES(2),
    .NUM_OPERANDS(1),
    .CONTROL_WIDTH($bits(Pu_inst::Fxv_opcd)),
    .THIS_UNIT_ID(VU_ID_LS)
  ) rs_ls (
    .clk,
    .reset,
    // insertion of new instructions
    .empty(rs_empty[VU_ID_LS]),
    .full(rs_full[VU_ID_LS]),
    .ready(unit_readies[VU_ID_LS]),
    .insert(unit_inserts[VU_ID_LS]),
    .control_in(q_op_out.xo),
    .operands(operands),
    .insert_ref(insert_refs[VU_ID_LS]),
    // requesting access to VRF
    .vrf_req(vrf_reqs[VU_ID_LS]),
    .vrf_ack(vrf_acks[VU_ID_LS]),
    // control info for VRF
    .vrf_addr(vrf_addrs[VU_ID_LS]),
    .vrf_en(vrf_ens[VU_ID_LS]),
    .vrf_we(vrf_wes[VU_ID_LS]),
    .vrf_ref(vrf_refs[VU_ID_LS]),
    // monitor on result bus
    .vrf_wb_en(vrf_wb_en),
    .vrf_wb_we(vrf_wb_we),
    .vrf_wb_addr(vrf_wb_addr),
    .vrf_wb_ref(vrf_wb_ref),
    // VCR read access
    .vcr_read(vcr_read_by_fus[VU_ID_LS]),
    .wb_vcr(wb_vcr),
    // enable operand input register during operand fetch
    .reg_in_en(slice_ctrl.vls_reg_in_en),
    // passing on operations to the datapath control logic
    .control_out({vls_xo}),
    .control_valid(vls_valid),
    .g(vls_g),
    .result_avail(vls_result_avail),
    .stall()
  );



  Vector_reservation_station #(
    .NUM_ENTRIES(2),
    .NUM_OPERANDS(1),
    .CONTROL_WIDTH($bits(Pu_inst::Fxv_opcd)),
    .THIS_UNIT_ID(VU_ID_CMP)
  ) rs_cmp (
    .clk,
    .reset,
    // insertion of new instructions
    .empty(rs_empty[VU_ID_CMP]),
    .full(rs_full[VU_ID_CMP]),
    .ready(unit_readies[VU_ID_CMP]),
    .insert(unit_inserts[VU_ID_CMP]),
    .control_in(q_op_out.xo),
    .operands(operands),
    .insert_ref(insert_refs[VU_ID_CMP]),
    // requesting access to VRF
    .vrf_req(vrf_reqs[VU_ID_CMP]),
    .vrf_ack(vrf_acks[VU_ID_CMP]),
    // control info for VRF
    .vrf_addr(vrf_addrs[VU_ID_CMP]),
    .vrf_en(vrf_ens[VU_ID_CMP]),
    .vrf_we(vrf_wes[VU_ID_CMP]),
    .vrf_ref(vrf_refs[VU_ID_CMP]),
    // monitor on result bus
    .vrf_wb_en(vrf_wb_en),
    .vrf_wb_we(vrf_wb_we),
    .vrf_wb_addr(vrf_wb_addr),
    .vrf_wb_ref(vrf_wb_ref),
    // VCR read access
    .vcr_read(vcr_read_by_fus[VU_ID_CMP]),
    .wb_vcr(wb_vcr),
    // enable operand input register during operand fetch
    .reg_in_en(slice_ctrl.cmp_reg_in_en),
    // passing on operations to the datapath control logic
    .control_out({cmp_xo}),
    .control_valid(cmp_valid),
    .g(cmp_g),
    .result_avail(cmp_result_avail),
    .stall()
  );


  Vector_reservation_station #(
    .NUM_ENTRIES(16),
    .NUM_OPERANDS(1),
    .CONTROL_WIDTH($bits(Pu_inst::Fxv_opcd) + $bits(Pu_inst::Fxv_cond)),
    .THIS_UNIT_ID(VU_ID_PLS)
  ) rs_pls (
    .clk,
    .reset,
    // insertion of new instructions
    .empty(rs_empty[VU_ID_PLS]),
    .full(rs_full[VU_ID_PLS]),
    .ready(unit_readies[VU_ID_PLS]),
    .insert(unit_inserts[VU_ID_PLS]),
    .control_in({q_op_out.xo, q_op_out.cond}),
    .operands(operands),
    .insert_ref(insert_refs[VU_ID_PLS]),
    // requesting access to VRF
    .vrf_req(vrf_reqs[VU_ID_PLS]),
    .vrf_ack(vrf_acks[VU_ID_PLS]),
    // control info for VRF
    .vrf_addr(vrf_addrs[VU_ID_PLS]),
    .vrf_en(vrf_ens[VU_ID_PLS]),
    .vrf_we(vrf_wes[VU_ID_PLS]),
    .vrf_ref(vrf_refs[VU_ID_PLS]),
    // monitor on result bus
    .vrf_wb_en(vrf_wb_en),
    .vrf_wb_we(vrf_wb_we),
    .vrf_wb_addr(vrf_wb_addr),
    .vrf_wb_ref(vrf_wb_ref),
    // VCR read access
    .vcr_read(vcr_read_by_fus[VU_ID_PLS]),
    .wb_vcr(wb_vcr),
    // enable operand input register during operand fetch
    .reg_in_en(slice_ctrl.pls_reg_in_en),
    // passing on operations to the datapath control logic
    .control_out({pls_xo, pls_cond}),
    .control_valid(pls_valid),
    .g(pls_g),
    .result_avail(pls_result_avail),
    .stall(pls_stall)
  );


  Vector_reservation_station #(
    .NUM_ENTRIES(2),
    .NUM_OPERANDS(2),
    .CONTROL_WIDTH($bits(Pu_inst::Fxv_opcd)+5+$bits(Vector::Permute_size)),
    .THIS_UNIT_ID(VU_ID_PERMUTE)
  ) rs_permute (
    .clk,
    .reset,
    // insertion of new instructions
    .empty(rs_empty[VU_ID_PERMUTE]),
    .full(rs_full[VU_ID_PERMUTE]),
    .ready(unit_readies[VU_ID_PERMUTE]),
    .insert(unit_inserts[VU_ID_PERMUTE]),
    .control_in({q_op_out.xo, q_op_out.rb, q_op_out.cond}),
    .operands(operands),
    .insert_ref(insert_refs[VU_ID_PERMUTE]),
    // requesting access to VRF
    .vrf_req(vrf_reqs[VU_ID_PERMUTE]),
    .vrf_ack(vrf_acks[VU_ID_PERMUTE]),
    // control info for VRF
    .vrf_addr(vrf_addrs[VU_ID_PERMUTE]),
    .vrf_en(vrf_ens[VU_ID_PERMUTE]),
    .vrf_we(vrf_wes[VU_ID_PERMUTE]),
    .vrf_ref(vrf_refs[VU_ID_PERMUTE]),
    // monitor on result bus
    .vrf_wb_en(vrf_wb_en),
    .vrf_wb_we(vrf_wb_we),
    .vrf_wb_addr(vrf_wb_addr),
    .vrf_wb_ref(vrf_wb_ref),
    // VCR read access
    .vcr_read(vcr_read_by_fus[VU_ID_PERMUTE]),
    .wb_vcr(wb_vcr),
    // enable operand input register during operand fetch
    .reg_in_en(slice_ctrl.permute_reg_in_en),
    // passing on operations to the datapath control logic
    .control_out({permute_xo, permute_shift, permute_size}),
    .control_valid(permute_valid),
    .g(permute_g),
    .result_avail(permute_result_avail),
    .stall(permute_stall)
  );



  //--------------------------------------------------------------------------------
  // Datapath control
  //--------------------------------------------------------------------------------

  Valu_ctrl #(
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .SCALAR_SIZE(SCALAR_SIZE),
    .MULT_STAGES(MULT_STAGES),
    .ADD_STAGES(ADD_STAGES)
  ) valu_controller (
    .clk,
    .reset,
    .valid(valu_valid),
    .xo(valu_xo),
    .cond(valu_cond),
    .stall(valu_stall),
    .result_avail(valu_result_avail),
    .ctrl(valu_ctrl),
    .ready(unit_readies[VU_ID_MADD])
  );


  Vector_ls_ctrl #(
    .NUM_SLICES(NUM_SLICES),
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .SCALAR_SIZE(SCALAR_SIZE)
  ) ls_controller (
    .clk,
    .reset,
    .valid(vls_valid),
    .xo(vls_xo),
    .g(vls_g),
    .result_avail(vls_result_avail),
    .ctrl(vls_ctrl),
    .ready(unit_readies[VU_ID_LS])
  );


  Vector_cmp_ctrl #(
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE)
  ) cmp_controller (
    .clk,
    .reset,
    .valid(cmp_valid),
    .xo(cmp_xo),
    .g(cmp_g),
    .result_avail(cmp_result_avail),
    .write_vcr(wb_vcr),
    .ctrl(cmp_ctrl),
    .ready(unit_readies[VU_ID_CMP])
  );

  Vector_pls_ctrl pls_controller (
    .clk,
    .reset,
    .valid(pls_valid),
    .xo(pls_xo),
    .cond(pls_cond),
    .result_avail(pls_result_avail),
    .stall(pls_stall),
    .ctrl(pls_ctrl),
    .ready(unit_readies[VU_ID_PLS]),
    .g(pls_g)
  );

  Vector_permute_ctrl permute_controller (
    .clk,
    .reset,
    .valid(permute_valid),
    .xo(permute_xo),
    .result_avail(permute_result_avail),
    .stall(permute_stall),
    .ctrl(permute_ctrl),
    .ready(unit_readies[VU_ID_PERMUTE]),
    .g(permute_g),
    .size(permute_size),
    .shift(permute_shift)
  );

  //--------------------------------------------------------------------------------
  // VRF control
  //--------------------------------------------------------------------------------

  //Vrf_wb_arb #(
    //.NUM_UNITS(NUM_UNITS)
  //) vrf_wb_arb (
    //.clk,
    //.reset,
    //.reqs(vrf_reqs),
    //.acks(vrf_acks),
    //.ens(vrf_ens),
    //.wes(vrf_wes),
    //.addrs(vrf_addrs),
    //.refs(vrf_refs),
    //.vrf_wb_en,
    //.vrf_wb_we,
    //.vrf_wb_addr,
    //.vrf_wb_ref,
    //.vrf_src_unit
  //);

  // arbitrate wb requests
  always_comb begin
    Unit_id winner;

    // default assignments
    vrf_wb_en = 1'b0;
    vrf_wb_we = 1'b0;
    vrf_wb_addr = '0;
    for(int i=0; i<$bits(vrf_acks); i++)
      vrf_acks[i] = 1'b0;
    winner = VU_ID_MADD;

    // arbitration
    if( vrf_req_mask[VU_ID_MADD] & vrf_reqs[VU_ID_MADD] )
      winner = VU_ID_MADD;
    else if( vrf_req_mask[VU_ID_CMP] & vrf_reqs[VU_ID_CMP] )
      winner = VU_ID_CMP;
    else if( vrf_req_mask[VU_ID_PERMUTE] & vrf_reqs[VU_ID_PERMUTE] )
      winner = VU_ID_PERMUTE;
    else if( vrf_req_mask[VU_ID_LS] & vrf_reqs[VU_ID_LS] )
      winner = VU_ID_LS;
    else if( vrf_req_mask[VU_ID_PLS] & vrf_reqs[VU_ID_PLS] )
      winner = VU_ID_PLS;

    vrf_wb_en = vrf_ens[winner];
    vrf_wb_we = vrf_wes[winner];
    vrf_wb_addr = vrf_addrs[winner];
    vrf_wb_ref = vrf_refs[winner];
    vrf_acks[winner] = vrf_reqs[winner];
    vrf_src_unit = unit_id_to_unit(winner);
  end

  always_comb begin
    // default assignment
    vrf_reqs_or_reduced = 1'b0;

    for(int i=0; i<$bits(vrf_reqs); i++)
      vrf_reqs_or_reduced |= vrf_reqs[i];
  end

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      for(int i=0; i<$bits(vrf_req_mask); i++)
        vrf_req_mask[i] <= 1'b1;
    end else begin
      if( vrf_reqs_or_reduced ) begin
        if( vrf_req_mask[$right(vrf_req_mask)] == 1'b0 ) begin
          for(int i=0; i<$bits(vrf_req_mask); i++)
            vrf_req_mask[i] <= 1'b1;
        end else begin
          for(int i=0; i<$bits(vrf_req_mask); i++) begin
            if( vrf_req_mask[i] == 1'b1 ) begin
              vrf_req_mask[i] <= 1'b0;
              break;
            end
          end
        end
      end
    end


  assign
    slice_ctrl.vrf_en = vrf_wb_en,
    slice_ctrl.vrf_addr = vrf_wb_addr,
    slice_ctrl.vrf_we = vrf_wb_we,
    slice_ctrl.vrf_src_unit = vrf_src_unit,
    slice_ctrl.vcr_we = wb_vcr;

  //--------------------------------------------------------------------------------
  // Assertions
  //--------------------------------------------------------------------------------

`ifndef SYNTHESIS
  property issue_only_vector_instructions;
    @(posedge clk) disable iff(reset)
    ( inst.valid |-> ir.fxv.opcd == Pu_inst::Op_nve_xo );
  endproperty

  assert property(issue_only_vector_instructions);


  property read_ra_or_rt_not_both;
    @(posedge clk) disable iff(reset)
    ( read_rt |-> !read_ra );
  endproperty

  assert property(read_ra_or_rt_not_both);


  generate
    genvar i;
    for(i=0; i<VRF_SIZE; i++) begin : gen_vrf
      property zero_vrf_readlock_when_pipe_empty;
        @(posedge clk) disable iff(reset)
        ( pipe_empty |-> (vrf_readlock[i] == 0) );
      endproperty

      assert property(zero_vrf_readlock_when_pipe_empty);
    end : gen_vrf
  endgenerate

  property zero_vcr_readlock_when_pipe_empty;
    @(posedge clk) disable iff(reset)
    ( pipe_empty |-> (vcr_readlock == 0) );
  endproperty

  assert property(zero_vcr_readlock_when_pipe_empty);

`endif  /* SYNTHESIS */

endmodule

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
