// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Fub_vector_test
  #(parameter bit DO_INST_SEQUENCE_TEST = 1,
    parameter int SINGLE_TEST_SIZE = 500, //10000,
    parameter int BULK_TEST_SIZE = 100, //10000,
    parameter int BULK_SIZE = 2)
  ();
  import Vector_tb::*;

  localparam int INST_SEQUENCE_SIZE = 17;
  //localparam int INST_SEQUENCE_SIZE = 2;
  localparam time clk_period = 10ns;
  localparam int NUM_SLICES = 8;
  localparam int NUM_ELEMS = 8;
  localparam int ELEM_SIZE = 16;
  localparam int VRF_SIZE = 32;
  localparam int MULT_STAGES = 4;
  localparam int ADD_STAGES = 1;
  localparam int MEM_ADDR_WIDTH = 12;
  localparam int PLS_WIDTH = NUM_SLICES * NUM_ELEMS * ELEM_SIZE;

  typedef Vector_predictor #(NUM_SLICES, NUM_ELEMS, ELEM_SIZE, VRF_SIZE) My_vector_predictor;
  //typedef Vector_state #(NUM_SLICES, NUM_ELEMS, ELEM_SIZE, VRF_SIZE) My_vector_state;

  logic clk, reset;
  bit error_flag;
  Pu_types::Word a, b;
  Frontend::Issue_slot inst;
  Frontend::Predecoded predec;
  logic ready;
  logic pipe_empty;
  Backend::Result_bus resbus;
  int cur_time = 0;


  always begin : clock_gen
    clk = 1'b0;
    #(clk_period/2);
    clk = 1'b1;
    #(clk_period/2);
  end


  //--------------------------------------------------------------------------------
  // Unit under test
  //--------------------------------------------------------------------------------

  Operand_if opbus();
  Bus_if #(.byteen(1'b1)) bus(.Clk(clk));
  Bus_if #(
    .byteen(1'b1),
    .data_width(PLS_WIDTH)
  ) pbus(.Clk(clk));

  Fub_vector #(
    .NUM_SLICES(NUM_SLICES),
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .VRF_SIZE(VRF_SIZE),
    .MULT_STAGES(MULT_STAGES),
    .ADD_STAGES(ADD_STAGES),
    .PLS_WIDTH(PLS_WIDTH)
  ) uut(
    .*
  );

  Iobus_dummy #(
    .RD_ACCEPT_LATENCY(0),
    .WR_ACCEPT_LATENCY(0),
    .RD_RETURN_LATENCY(0),
    .WR_RETURN_LATENCY(0),
    .RESPONSE_FUNCTION(1),  // work as memory
    .BYTE_ENABLED(1'b1)
  ) mem (
    .clk,
    .reset,
    .iobus(bus)
  );

  Iobus_dummy #(
    .RD_ACCEPT_LATENCY(0),
    .WR_ACCEPT_LATENCY(0),
    .RD_RETURN_LATENCY(0),
    .WR_RETURN_LATENCY(0),
    .RESPONSE_FUNCTION(1),  // work as memory
    .BYTE_ENABLED(1'b1),
    .DATA_WIDTH(PLS_WIDTH),
    .MEM_DEFAULT({PLS_WIDTH{1'b0}})
  ) pmem (
    .clk,
    .reset,
    .iobus(pbus)
  );


  //--------------------------------------------------------------------------------
  // Specialization of Rand_state to ensure useful register contents for addressing
  //--------------------------------------------------------------------------------

  class Pu_rand_state extends Sit::Rand_state;
    constraint gprs_for_addressing {
      foreach(gpr[i])
        gpr[i] < addr_space_size/2;
    }

    function new(input Sit::Mem_model _mem_model,
        Sit::Mem_model _io_model,
        input int addr_space_size = 2**32,
        input int io_space_size = 2**32);
      super.new(_mem_model, _io_model, addr_space_size, io_space_size);
    endfunction
  endclass


  //--------------------------------------------------------------------------------
  // Procedural test
  //--------------------------------------------------------------------------------

  task automatic set_state(const ref My_vector_predictor::My_vector_state state,
      input Sit::State pu_state);
    Pu_types::Address iter;
    Pu_types::Word mem_word;

    assert(NUM_SLICES == 8) else $fatal("modify code to use NUM_SLICES != 8");

    for(int reg_i=0; reg_i<VRF_SIZE; reg_i++) begin
      uut.gen_slice[0].slice.vrf.regs[reg_i] = {>>{state.vrf[0][reg_i]}};
      uut.gen_slice[1].slice.vrf.regs[reg_i] = {>>{state.vrf[1][reg_i]}};
      uut.gen_slice[2].slice.vrf.regs[reg_i] = {>>{state.vrf[2][reg_i]}};
      uut.gen_slice[3].slice.vrf.regs[reg_i] = {>>{state.vrf[3][reg_i]}};
      uut.gen_slice[4].slice.vrf.regs[reg_i] = {>>{state.vrf[4][reg_i]}};
      uut.gen_slice[5].slice.vrf.regs[reg_i] = {>>{state.vrf[5][reg_i]}};
      uut.gen_slice[6].slice.vrf.regs[reg_i] = {>>{state.vrf[6][reg_i]}};
      uut.gen_slice[7].slice.vrf.regs[reg_i] = {>>{state.vrf[7][reg_i]}};
      // because SystemVerilog...
    end

    uut.gen_slice[0].slice.valu.accumulator = {>>{state.accumulator[0]}};
    uut.gen_slice[1].slice.valu.accumulator = {>>{state.accumulator[1]}};
    uut.gen_slice[2].slice.valu.accumulator = {>>{state.accumulator[2]}};
    uut.gen_slice[3].slice.valu.accumulator = {>>{state.accumulator[3]}};
    uut.gen_slice[4].slice.valu.accumulator = {>>{state.accumulator[4]}};
    uut.gen_slice[5].slice.valu.accumulator = {>>{state.accumulator[5]}};
    uut.gen_slice[6].slice.valu.accumulator = {>>{state.accumulator[6]}};
    uut.gen_slice[7].slice.valu.accumulator = {>>{state.accumulator[7]}};

    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) uut.gen_slice[0].slice.vcr[elem_i] = state.vcr[0][elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) uut.gen_slice[1].slice.vcr[elem_i] = state.vcr[1][elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) uut.gen_slice[2].slice.vcr[elem_i] = state.vcr[2][elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) uut.gen_slice[3].slice.vcr[elem_i] = state.vcr[3][elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) uut.gen_slice[4].slice.vcr[elem_i] = state.vcr[4][elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) uut.gen_slice[5].slice.vcr[elem_i] = state.vcr[5][elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) uut.gen_slice[6].slice.vcr[elem_i] = state.vcr[6][elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) uut.gen_slice[7].slice.vcr[elem_i] = state.vcr[7][elem_i];


    for(int i=0; i<2**MEM_ADDR_WIDTH; i++) begin
      mem.mem[i] = pu_state.get_mem_model().get(i);
    end

    if( state.pmem.first(iter) )
      do
        pmem.mem[iter] = state.pmem[iter];
      while( state.pmem.next(iter) );
  endtask

  task automatic get_state(ref My_vector_predictor::My_vector_state state,
      input Sit::State pu_state);
    Pu_types::Address iter;

    assert(NUM_SLICES == 8) else $fatal("modify code to use NUM_SLICES != 8");

    for(int reg_i=0; reg_i<VRF_SIZE; reg_i++) begin
      {>>{state.vrf[0][reg_i]}} = uut.gen_slice[0].slice.vrf.regs[reg_i];
      {>>{state.vrf[1][reg_i]}} = uut.gen_slice[1].slice.vrf.regs[reg_i];
      {>>{state.vrf[2][reg_i]}} = uut.gen_slice[2].slice.vrf.regs[reg_i];
      {>>{state.vrf[3][reg_i]}} = uut.gen_slice[3].slice.vrf.regs[reg_i];
      {>>{state.vrf[4][reg_i]}} = uut.gen_slice[4].slice.vrf.regs[reg_i];
      {>>{state.vrf[5][reg_i]}} = uut.gen_slice[5].slice.vrf.regs[reg_i];
      {>>{state.vrf[6][reg_i]}} = uut.gen_slice[6].slice.vrf.regs[reg_i];
      {>>{state.vrf[7][reg_i]}} = uut.gen_slice[7].slice.vrf.regs[reg_i];
    end

    {>>{state.accumulator[0]}} = uut.gen_slice[0].slice.valu.accumulator;
    {>>{state.accumulator[1]}} = uut.gen_slice[1].slice.valu.accumulator;
    {>>{state.accumulator[2]}} = uut.gen_slice[2].slice.valu.accumulator;
    {>>{state.accumulator[3]}} = uut.gen_slice[3].slice.valu.accumulator;
    {>>{state.accumulator[4]}} = uut.gen_slice[4].slice.valu.accumulator;
    {>>{state.accumulator[5]}} = uut.gen_slice[5].slice.valu.accumulator;
    {>>{state.accumulator[6]}} = uut.gen_slice[6].slice.valu.accumulator;
    {>>{state.accumulator[7]}} = uut.gen_slice[7].slice.valu.accumulator;

    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) state.vcr[0][elem_i] = uut.gen_slice[0].slice.vcr[elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) state.vcr[1][elem_i] = uut.gen_slice[1].slice.vcr[elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) state.vcr[2][elem_i] = uut.gen_slice[2].slice.vcr[elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) state.vcr[3][elem_i] = uut.gen_slice[3].slice.vcr[elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) state.vcr[4][elem_i] = uut.gen_slice[4].slice.vcr[elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) state.vcr[5][elem_i] = uut.gen_slice[5].slice.vcr[elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) state.vcr[6][elem_i] = uut.gen_slice[6].slice.vcr[elem_i];
    for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) state.vcr[7][elem_i] = uut.gen_slice[7].slice.vcr[elem_i];

    for(int i=0; i<2**MEM_ADDR_WIDTH; i++) begin
      pu_state.get_mem_model().set(i, mem.mem[i]);
    end

    if( pmem.mem.first(iter) )
      do
        state.pmem[iter] = pmem.mem[iter];
      while( pmem.mem.next(iter) );
  endtask

  function automatic bit is_state_equal(input Vector_state va, vb, input Sit::State ga, gb);
    bit vequal;
    bit pequal;

    vequal = va.is_equal_to(vb);
    pequal = Sit::compare_mem(ga.get_mem_model(), gb.get_mem_model());

    return vequal && pequal;
  endfunction

  /**
   * Send one instruction to the functional unit.
   */
  task automatic issue_instruction(input Vector_instruction vinst, input Sit::State pu_state);
    inst.ir <= vinst.get();
    inst.pc <= 0;
    inst.npc <= 1;

    predec <= predecode_vector(vinst);

    fork
    begin
      @(posedge clk);
      opbus.opbus_0.a <= pu_state.get_gpr(vinst.ra);
      opbus.opbus_0.b <= pu_state.get_gpr(vinst.rb);
    end
    join_none

    do begin
      inst.valid <= ready;
      @(posedge clk);
    end while( !ready );
    inst.valid <= 1'b0;
  endtask


  task automatic execute_single_instruction(const ref Vector_instruction vinst,
      const ref My_vector_predictor::My_vector_state vstate,
      input Sit::State pu_state,
      ref My_vector_predictor::My_vector_state vstate_res,
      input Sit::State pu_state_res);
    set_state(vstate, pu_state);
    issue_instruction(vinst, pu_state);
    do
      @(posedge clk);
    while( !pipe_empty );
    get_state(vstate_res, pu_state_res);
  endtask


  initial begin
    import Pu_inst::*;

    bit success;
    Sit::Sparse_mem_model memory;
    Sit::Sparse_mem_model memory_res;
    Sit::Static_mem_model io_mem;
    Pu_rand_state pu_state;
    Pu_rand_state pu_state_res;
    Vector_instruction vinst;
    My_vector_predictor::My_vector_state vstate;
    My_vector_predictor::My_vector_state vstate_res;
    My_vector_predictor predictor;
    Vector_instruction inst_sequence[INST_SEQUENCE_SIZE][];
    real percent_complete;

    error_flag = 0;
    success = 1;
    memory = new (2**MEM_ADDR_WIDTH, .default_random(1'b1));
    memory_res = new (2**MEM_ADDR_WIDTH);
    io_mem = new ('x);
    pu_state = new (memory, io_mem,
        .addr_space_size(2**MEM_ADDR_WIDTH));
    pu_state_res = new (memory_res, io_mem,
        .addr_space_size(2**MEM_ADDR_WIDTH));
    vstate = new ();
    vstate_res = new ();
    vinst = new ();
    predictor = new ();

    //inst_sequence[0] = new [1];
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmabm);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmatacbm);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmulbm);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmultacbm);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvsubbm);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvaddactacb);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvaddacbm);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvaddtacb);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvaddbm);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmtacb);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvcmpb);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvsplatb);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmabfs);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmatacbfs);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmulbfs);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmultacbfs);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvsubbfs);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvaddactacbf);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvaddacbfs);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvaddbfs);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmtacbf);


    // load sequence
    inst_sequence[0] = new [1];
    inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvlax);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvstax);
    //inst_sequence[0][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmahm);

    // mult-acc sequence
    inst_sequence[1] = new [4];
    //inst_sequence[1][0] = new (Op_nve_xo, 1, 0, 2, Xop_fxvmahm);
    inst_sequence[1][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmahm);
    inst_sequence[1][1] = new (Op_nve_xo, 3, 0, 1, Xop_fxvmahm);
    inst_sequence[1][2] = new (Op_nve_xo, 4, 0, 3, Xop_fxvmahm);
    inst_sequence[1][3] = new (Op_nve_xo, 5, 3, 4, Xop_fxvmahm);


    // store sequence
    inst_sequence[2] = new [1];
    inst_sequence[2][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvstax);

    // load-add-store sequence
    inst_sequence[3] = new [4];
    inst_sequence[3][0] = new (Op_nve_xo, 0, 0, 1, Xop_fxvlax);
    inst_sequence[3][1] = new (Op_nve_xo, 1, 0, 2, Xop_fxvlax);
    inst_sequence[3][2] = new (Op_nve_xo, 2, 0, 1, Xop_fxvmahm);
    inst_sequence[3][3] = new (Op_nve_xo, 2, 0, 0, Xop_fxvstax);

    // compare sequence
    inst_sequence[4] = new [3];
    inst_sequence[4][0] = new (Op_nve_xo, 0, 0, 0, Xop_fxvcmph);
    inst_sequence[4][1] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmahm);
    inst_sequence[4][2] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmahm, Fxv_cond_gt);

    // load, store sequence
    inst_sequence[5] = new [2];
    inst_sequence[5][0] = new (Op_nve_xo, 0, 0, 0, Xop_fxvlax);
    inst_sequence[5][1] = new (Op_nve_xo, 1, 0, 1, Xop_fxvstax);

    // mtach sequence
    inst_sequence[6] = new [3];
    inst_sequence[6][0] = new (Op_nve_xo, 0, 0, 0, Xop_fxvmtach);
    inst_sequence[6][1] = new (Op_nve_xo, 1, 0, 0, Xop_fxvmahm);
    inst_sequence[6][2] = new (Op_nve_xo, 2, 0, 0, Xop_fxvmahm);

    // add sequence
    inst_sequence[7] = new [1];
    inst_sequence[7][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvaddhm);

    // stdp kernel sequence
    inst_sequence[8] = new [7];
    inst_sequence[8][0] = new (Op_nve_xo,  1,  1,  2, Xop_fxvsubhm);
    inst_sequence[8][1] = new (Op_nve_xo, 10,  1, 10, Xop_fxvcmph);
    inst_sequence[8][2] = new (Op_nve_xo,  2, 31,  0, Xop_fxvsubhm);
    inst_sequence[8][3] = new (Op_nve_xo,  3, 29,  0, Xop_fxvmulhm);
    inst_sequence[8][4] = new (Op_nve_xo, 10,  0, 10, Xop_fxvmtach);
    inst_sequence[8][5] = new (Op_nve_xo,  0,  1,  2, Xop_fxvmahm, Fxv_cond_gt);
    inst_sequence[8][6] = new (Op_nve_xo,  0,  1,  3, Xop_fxvmahm, Fxv_cond_lt);

    // input/output test
    inst_sequence[9] = new [2];
    inst_sequence[9][0] = new (Op_nve_xo, 0, 0, 0, Xop_fxvinx);
    inst_sequence[9][1] = new (Op_nve_xo, 0, 0, 1, Xop_fxvoutx);

    // pack/unpack test
    inst_sequence[10] = new [4];
    inst_sequence[10][0] = new (Op_nve_xo, 31, 1, 2, Xop_fxvpckbu);
    inst_sequence[10][1] = new (Op_nve_xo, 30, 1, 2, Xop_fxvpckbl);
    inst_sequence[10][2] = new (Op_nve_xo, 29, 1, 2, Xop_fxvupckbl);
    inst_sequence[10][3] = new (Op_nve_xo, 28, 1, 2, Xop_fxvupckbr);

    // saturating fractional math
    inst_sequence[11] = new [5];
    inst_sequence[11][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmulhfs);
    inst_sequence[11][1] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmahfs);
    inst_sequence[11][2] = new (Op_nve_xo, 4, 5, 6, Xop_fxvmatachfs);
    inst_sequence[11][3] = new (Op_nve_xo, 0, 1, 2, Xop_fxvsubhfs);
    inst_sequence[11][4] = new (Op_nve_xo, 7, 8, 9, Xop_fxvmultachfs);

    inst_sequence[12] = new [1];
    inst_sequence[12][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmatachfs);

    inst_sequence[13] = new [2];
    inst_sequence[13][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvupckbl, Fxv_cond_gt);
    inst_sequence[13][1] = new (Op_nve_xo, 0, 1, 2, Xop_fxvupckbr, Fxv_cond_gt);

    inst_sequence[14] = new [1];
    inst_sequence[14][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvmabm);

    inst_sequence[15] = new [2];
    inst_sequence[15][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvpckbu, Fxv_cond_gt);
    inst_sequence[15][1] = new (Op_nve_xo, 3, 4, 5, Xop_fxvsplath);

    inst_sequence[16] = new [10];
    inst_sequence[16][0] = new (Op_nve_xo, 0, 1, 2, Xop_fxvshb);
    inst_sequence[16][1] = new (Op_nve_xo, 0, 1, 2, Xop_fxvshb);
    inst_sequence[16][2] = new (Op_nve_xo, 0, 1, 2, Xop_fxvshb);
    inst_sequence[16][3] = new (Op_nve_xo, 0, 1, 2, Xop_fxvshb);
    inst_sequence[16][4] = new (Op_nve_xo, 0, 1, 2, Xop_fxvshb);
    inst_sequence[16][5] = new (Op_nve_xo, 0, 1, 2, Xop_fxvshb);
    inst_sequence[16][6] = new (Op_nve_xo, 0, 1, 2, Xop_fxvshb);
    inst_sequence[16][7] = new (Op_nve_xo, 0, 1, 2, Xop_fxvshb);
    inst_sequence[16][8] = new (Op_nve_xo, 0, 1, 2, Xop_fxvshb);
    inst_sequence[16][9] = new (Op_nve_xo, 0, 1, 2, Xop_fxvshb);


    reset = 1'b1;
    a = 0;
    b = 0;

    #(10*clk_period);
    @(posedge clk) reset = 1'b0;


    //--------------------------------------------------------------------------------
    //  fixed sequence test
    //--------------------------------------------------------------------------------

    if( DO_INST_SEQUENCE_TEST ) begin : inst_sequence_test
      if( INST_SEQUENCE_SIZE > 0 )
        $display("=== fixed instruction sequence test (num=%3d) ===", INST_SEQUENCE_SIZE);

      for(int seq_i=0; seq_i<INST_SEQUENCE_SIZE; seq_i++) begin
        void'(vstate.randomize());
        void'(pu_state.randomize());
        set_state(vstate, pu_state);

        for(int i=0; i<inst_sequence[seq_i].size(); i++) begin
          predictor.predict(inst_sequence[seq_i][i], vstate, pu_state);
          issue_instruction(inst_sequence[seq_i][i], pu_state);
        end

        do
          @(posedge clk);
        while( !pipe_empty );

        get_state(vstate_res, pu_state_res);

        assert(is_state_equal(vstate_res, vstate, pu_state_res, pu_state) ) else
        begin
          $error("fixed sequence no. %2d did not yield correct result",
              seq_i);
          success = 0;
          error_flag = 1;
          $display("msg from predictor:\n%s", predictor.msg);
        end

        predictor.clear_msg();
      end
    end


    //--------------------------------------------------------------------------------
    // single instruction test
    //--------------------------------------------------------------------------------

    if( SINGLE_TEST_SIZE > 0 )
      $display("=== single instruction test (num=%3d) ===", SINGLE_TEST_SIZE);

    percent_complete = 0.0;
    for(int i=0; i<SINGLE_TEST_SIZE; i++) begin
      if( real'(i) / real'(SINGLE_TEST_SIZE) - percent_complete > 0.1 ) begin
        percent_complete = real'(i) / real'(SINGLE_TEST_SIZE);
        $display("%3.1f %% complete", 100.0 * percent_complete);
      end

      check_randomize_vinst: assert(vinst.randomize());
      //check_randomize_vinst: assert(vinst.randomize() with {
        //xo != Xop_fxvcmpb
        //&& xo != Xop_fxvcmph;
      //});
      check_ranomize_vstate: assert(vstate.randomize());
      check_randomize_pu_state: assert(pu_state.randomize());

      execute_single_instruction(vinst, vstate, pu_state, vstate_res, pu_state_res);
      predictor.predict(vinst, vstate, pu_state);

      assert(is_state_equal(vstate_res, vstate, pu_state_res, pu_state)) else
      begin
        $display("single instruction test failed for instruction no. %2d",
            i);
        success = 0;
        error_flag = 1;
        //$display("==== FAILED INSTRUCTION BEGIN ====");
        //$display("state before instruction:");
        //vstate.print();
        //$display("state after instruction:");
        //vstate_res.print();
        //$display("predicted state:");
        //vstate_pred.print();
        //$display("==== FAILED INSTRUCTION END ====");

        $display("msg from predictor:\n%s", predictor.msg);
      end

      predictor.clear_msg();
    end

    while( !pipe_empty ) @(posedge clk);


    //--------------------------------------------------------------------------------
    // bulk test
    //--------------------------------------------------------------------------------

    if( BULK_TEST_SIZE > 0 )
      $display("=== bulk instruction test with bulk size = %3d (num=%3d) ===",
          BULK_SIZE, BULK_TEST_SIZE);

    percent_complete = 0.0;
    for(int i=0; i<BULK_TEST_SIZE; i++) begin
      if( real'(i) / real'(BULK_TEST_SIZE) - percent_complete > 0.1 ) begin
        percent_complete = real'(i) / real'(BULK_TEST_SIZE);
        $display("%3.1f %% complete", percent_complete*100.0);
      end

      check_randomize_vstate: assert(vstate.randomize());
      check_randomize_pu_state: assert(pu_state.randomize());

      set_state(vstate, pu_state);

      for(int j=0; j<BULK_SIZE; j++) begin
        check_randomize_vinst: assert(vinst.randomize());
        //check_randomize_vinst: assert(vinst.randomize() with {
          //!(xo inside {
            //Pu_inst::Xop_fxvpckbu,
            //Pu_inst::Xop_fxvpckbl,
            //Pu_inst::Xop_fxvupckbr,
            //Pu_inst::Xop_fxvupckbl,
            //Pu_inst::Xop_fxvsel,
            //Pu_inst::Xop_fxvsplath,
            //Pu_inst::Xop_fxvsplatb,
            //Pu_inst::Xop_fxvshh,
            //Pu_inst::Xop_fxvshb
          //});
        //});

        predictor.predict(vinst, vstate, pu_state);
        issue_instruction(vinst, pu_state);
      end

      do
        @(posedge clk);
      while( !pipe_empty );

      get_state(vstate_res, pu_state_res);

      assert(is_state_equal(vstate_res, vstate, pu_state_res, pu_state)) else
      begin
        $error("block no. %3d containing %2d instructions did not yield correct result", i, BULK_SIZE);
        success = 0;
        error_flag = 1;

        $display("msg from predictor:\n%s", predictor.msg);
      end

      predictor.clear_msg();
    end


    $display("=== All done. ===");
    if( success )
      $display("NO ERRORS");
    else
      $display("ERRORS DETECTED");
    $stop;
  end


  always begin
    #(1ms);
    cur_time = cur_time + 1;
    $display("=== 1ms tick: time = %d ms ===", cur_time);
  end

endmodule

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
