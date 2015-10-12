// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


//% @brief FXV vector functional unit
//%
//% This is a SIMD unit for fixed-point operations and IO.
//%
module Fub_vector
  #(parameter int NUM_SLICES = 1,
    parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int VRF_SIZE = 32,
    parameter int MULT_STAGES = 1,
    parameter int ADD_STAGES = 1,
    parameter int INST_QUEUE_DEPTH = 5,
    parameter int PLS_WIDTH = 128 )
  ( input logic clk, reset,
    input Frontend::Issue_slot inst,
    input Frontend::Predecoded predec,
    output logic ready,
    output logic pipe_empty,
    Operand_if.read opbus,
    output Backend::Result_bus resbus,
    Bus_if.master bus,
    Bus_if.master pbus);

  import Pu_types::*;

  
  localparam int PLS_BYTE_WIDTH = PLS_WIDTH / 8;
  localparam int ELEM_BYTE_SIZE = ELEM_SIZE / 8;

  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------
  
  Word aa, bb;

  Word load_in;
  Word store_serial_in[0:NUM_ELEMS-1];
  Word store_serial_out[0:NUM_ELEMS-1];


  //--------------------------------------------------------------------------------
  // global logic
  //--------------------------------------------------------------------------------
  
  always_comb aa = opbus.opbus_0.a;
  always_comb bb = opbus.opbus_0.b;


  //--------------------------------------------------------------------------------
  // datapath control logic
  //--------------------------------------------------------------------------------

  Vector_slice_ctrl_if #(
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .VRF_SIZE(VRF_SIZE)
  ) slice_ctrl_if();

  Valu_ctrl_if #(
    .NUM_ELEMS(NUM_ELEMS),
    .MULT_STAGES(MULT_STAGES),
    .ADD_STAGES(ADD_STAGES)
  ) valu_ctrl_if();

  Vector_ls_ctrl_if #(
    .NUM_SLICES(NUM_SLICES),
    .NUM_ELEMS(NUM_ELEMS),
    .SCALAR_SIZE($bits(Word)),
    .ELEM_SIZE(ELEM_SIZE)
  ) vls_ctrl_if();

  Vector_cmp_ctrl_if cmp_ctrl_if();

  Vector_pls_ctrl_if #(
    .BUS_ADDR_WIDTH(32),
    .BUS_DATA_WIDTH(NUM_ELEMS*ELEM_SIZE*NUM_SLICES)
  ) pls_ctrl_if();

  Vector_permute_ctrl_if permute_ctrl_if();


  Vector_ctrl #(
    .NUM_SLICES(NUM_SLICES),
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .VRF_SIZE(VRF_SIZE),
    .SCALAR_SIZE($bits(Word)),
    .MULT_STAGES(MULT_STAGES),
    .ADD_STAGES(ADD_STAGES),
    .MAX_IN_FLIGHT(INST_QUEUE_DEPTH)
  ) ctrl (
    .clk,
    .reset,
    .inst,
    .a(aa),
    .b(bb),
    .ready,
    .pipe_empty,
    .slice_ctrl(slice_ctrl_if.ctrl),
    .valu_ctrl(valu_ctrl_if.ctrl),
    .vls_ctrl(vls_ctrl_if.ctrl),
    .cmp_ctrl(cmp_ctrl_if.ctrl),
    .pls_ctrl(pls_ctrl_if.ctrl),
    .permute_ctrl(permute_ctrl_if.ctrl)
  );

  //--------------------------------------------------------------------------------
  // slices
  //--------------------------------------------------------------------------------

  generate
    genvar slice_i;
    for(slice_i=0; slice_i<NUM_SLICES; slice_i++) begin : gen_slice

      logic[NUM_ELEMS*ELEM_SIZE-1:0] sdata;
      logic[NUM_ELEMS*ELEM_SIZE-1:0] mdata;
      logic[NUM_ELEMS*ELEM_BYTE_SIZE-1:0] mbyteen;

      Vector_slice #(
        .THIS_SLICE(slice_i),
        .NUM_ELEMS(NUM_ELEMS),
        .ELEM_SIZE(ELEM_SIZE),
        .VRF_SIZE(VRF_SIZE),
        .SCALAR_SIZE($bits(Pu_types::Word)),
        .MULT_STAGES(MULT_STAGES),
        .ADD_STAGES(ADD_STAGES)
      ) slice (
        .clk,
        .reset,
        .ctrl(slice_ctrl_if.slice),
        .valu_ctrl(valu_ctrl_if.valu),
        .vls_ctrl(vls_ctrl_if.vls),
        .cmp_ctrl(cmp_ctrl_if.cmp),
        .pls_ctrl(pls_ctrl_if.pls),
        .permute_ctrl(permute_ctrl_if.permute),
        .load_in,
        .store_serial_in(store_serial_in[slice_i]),
        .store_serial_out(store_serial_out[slice_i]),
        .sdata(sdata),
        .mdata(mdata),
        .mbyteen(mbyteen)
      );


      if( slice_i < NUM_SLICES-1 ) begin : gen_store_bus

        assign store_serial_in[slice_i] = store_serial_out[slice_i+1];

      end : gen_store_bus


      always_comb begin
        sdata = pbus.SData[PLS_WIDTH - slice_i * (ELEM_SIZE*NUM_ELEMS) -1 -: ELEM_SIZE * NUM_ELEMS];
        pbus.MData[PLS_WIDTH - slice_i * (ELEM_SIZE*NUM_ELEMS) -1 -: ELEM_SIZE * NUM_ELEMS] = mdata;
        pbus.MByteEn[PLS_BYTE_WIDTH - slice_i * (ELEM_BYTE_SIZE*NUM_ELEMS) -1 -: ELEM_BYTE_SIZE * NUM_ELEMS] = mbyteen;
      end
    end : gen_slice
  endgenerate


  //--------------------------------------------------------------------------------
  // vector load/store shared part
  //--------------------------------------------------------------------------------
  
  Vector_ls_shared #(
    .NUM_SLICES(NUM_SLICES),
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .SCALAR_SIZE($bits(Pu_types::Word))
  ) ls_shared (
    .clk,
    .reset,
    .ctrl(vls_ctrl_if.shared),
    .bus(bus),
    .load_out(load_in),
    .store_serial_in(store_serial_out[0])
  );


  //--------------------------------------------------------------------------------
  // parallel load/store shared part
  //--------------------------------------------------------------------------------
  
  Vector_pls_shared pls_shared (
    .clk,
    .reset,
    .ctrl(pls_ctrl_if.shared),
    .pbus(pbus)
  );


`ifndef SYNTHESIS

  //--------------------------------------------------------------------------------
  // assertions
  //--------------------------------------------------------------------------------

  initial begin
    assert($bits(pbus.MData) == PLS_WIDTH) else
      $error("width mismatch between pbus interface and parameter. (pbus.MData is %d bits, PLS_WIDTH = %d)",
        $bits(pbus.MData), PLS_WIDTH);
  end 


  //--------------------------------------------------------------------------------
  // coverage
  //--------------------------------------------------------------------------------
  
  covergroup cg_operations @(posedge clk);
    option.per_instance = 1;

    xo: coverpoint inst.ir.fxv.xo iff(!reset && inst.valid) {
      ignore_bins ignore_null = { Pu_inst::Xop_fxv_null };
    }
  endgroup

  cg_operations cg_operations_inst = new();


`endif  /* !SYNTHESIS */

endmodule

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
