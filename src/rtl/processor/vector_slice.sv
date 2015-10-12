// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_slice
  #(parameter int THIS_SLICE = 0,
    parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int ENABLES_PER_ELEMENT = 4,
    parameter int VRF_SIZE = 32,
    parameter int SCALAR_SIZE = 32,
    parameter int MULT_STAGES = 1,
    parameter int ADD_STAGES = 1 )
  ( input logic clk, reset,
    Vector_slice_ctrl_if.slice ctrl,
    Valu_ctrl_if.valu valu_ctrl,
    Vector_ls_ctrl_if.vls vls_ctrl,
    Vector_cmp_ctrl_if.cmp cmp_ctrl,
    Vector_pls_ctrl_if.pls pls_ctrl,
    Vector_permute_ctrl_if.permute permute_ctrl,
    input logic[SCALAR_SIZE-1:0] load_in,
    input logic[SCALAR_SIZE-1:0] store_serial_in,
    output logic[SCALAR_SIZE-1:0] store_serial_out,
    input logic[NUM_ELEMS*ELEM_SIZE-1:0] sdata,
    output logic[NUM_ELEMS*ELEM_SIZE-1:0] mdata,
    output logic[(NUM_ELEMS*ELEM_SIZE / 8)-1:0] mbyteen );

  import Vector::*;

  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------

  typedef logic[NUM_ELEMS*ELEM_SIZE-1:0] Vector_raw;
  typedef logic[0:ENABLES_PER_ELEMENT-1] Element_enables[0:NUM_ELEMS-1];
  typedef Compare[0:NUM_ELEMS-1] Vector_condition_register;


  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------

  Vector_raw vrf_in;
  Vector_raw vrf_in_from_valu;
  Vector_raw vrf_in_from_vls;
  Vector_raw vrf_in_from_pls;
  Vector_raw vrf_in_from_permute;
  Vector_raw vrf_out;
  Vector_raw valu_in_a_d;
  Vector_raw valu_in_b_d;
  Vector_raw vls_in_d;
  Vector_raw cmp_in_d;
  Vector_raw permute_in_a_d;
  Vector_raw permute_in_b_d;
  Element_enables vrf_write_mask;
  Element_enables vrf_write_mask_from_valu;
  Element_enables vrf_write_mask_from_pls;
  Vector_condition_register vcr, vcr_out;
  //Compare vcr_tmp[0:NUM_ELEMS-1];

  //--------------------------------------------------------------------------------
  // Vector Condition Register
  //--------------------------------------------------------------------------------

  /*always_comb begin : select_element_enable
    for(int i=0; i<NUM_ELEMS; i++)
      elem_en[i] = vcr[i].gt;
      //unique case(ctrl.vcr_enable_mode)
        //CMP_EQ: elem_en[i] = vcr[i].eq;
        //CMP_GT: elem_en[i] = vcr[i].gt;
        //CMP_LT: elem_en[i] = vcr[i].lt;
        //default elem_en[i] = 1'bx;
      //endcase
  end*/

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      for(int i=0; i<NUM_ELEMS; i++)
        vcr[i] <= '0;
    end else begin
      if( ctrl.vcr_we ) begin
        for(int i=0; i<NUM_ELEMS; i++)
          vcr[i] <= vcr_out[i];
      end
    end


  //--------------------------------------------------------------------------------
  // Vector Register File
  //--------------------------------------------------------------------------------

  always_comb
    unique case(ctrl.vrf_src_unit)
      VU_MADD: begin
        vrf_in = vrf_in_from_valu;
        vrf_write_mask = vrf_write_mask_from_valu;
      end

      VU_LS: begin
        vrf_in = vrf_in_from_vls;
        for(int i=0; i<NUM_ELEMS; i++)
          vrf_write_mask[i] = '1;
      end

      VU_PLS: begin
        vrf_in = vrf_in_from_pls;
        vrf_write_mask = vrf_write_mask_from_pls;
      end

      VU_PERMUTE: begin
        vrf_in = vrf_in_from_permute;
        for(int i=0; i<NUM_ELEMS; i++)
          vrf_write_mask[i] = '1;
      end

      default: begin
        vrf_in = 'x;
        for(int i=0; i<NUM_ELEMS; i++)
          vrf_write_mask[i] = 'x;
      end
    endcase

  Vector_rf #(
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .ENABLES_PER_ELEMENT(ENABLES_PER_ELEMENT),
    .VRF_SIZE(VRF_SIZE)
  ) vrf (
    .clk,
    .reset,
    .en(ctrl.vrf_en),
    .write_mask(vrf_write_mask),
    .addr(ctrl.vrf_addr),
    .we(ctrl.vrf_we),
    .data_r(vrf_out),
    .data_w(vrf_in)
  );


  //--------------------------------------------------------------------------------
  // Vector Arithmetic Logic Unit
  //--------------------------------------------------------------------------------

  always_ff @(posedge clk) begin
  //always_latch begin
    if( ctrl.valu_reg_in_en[0] )
      valu_in_a_d <= vrf_out;

    if( ctrl.valu_reg_in_en[1] )
      valu_in_b_d <= vrf_out;
  end

  /*always_comb begin
    for(int i=0; i<NUM_ELEMS; i++) begin
      vcr_tmp[i].gt = '1;
      vcr_tmp[i].lt = '0;
      vcr_tmp[i].eq = '0;
    end
  end*/

  Valu #(
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .ENABLES_PER_ELEMENT(ENABLES_PER_ELEMENT),
    .SCALAR_SIZE(SCALAR_SIZE),
    .MULT_STAGES(MULT_STAGES),
    .ADD_STAGES(ADD_STAGES)
  ) valu (
    .clk,
    .reset,
    .ctrl(valu_ctrl),
    .vcr(vcr),
    .a(valu_in_a_d),
    .b(valu_in_b_d),
    //.b(vrf_out),
    .g('b0),
    .y(vrf_in_from_valu),
    .write_mask(vrf_write_mask_from_valu)
  );


  //--------------------------------------------------------------------------------
  // Vector Load/Store unit
  //--------------------------------------------------------------------------------

  always_ff @(posedge clk) begin
  //always_latch begin
    if( ctrl.vls_reg_in_en[0] )
      vls_in_d = vrf_out;
  end

  Vector_ls #(
    .THIS_SLICE(THIS_SLICE),
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .VRF_SIZE(VRF_SIZE),
    .SCALAR_SIZE(SCALAR_SIZE)
  ) vls (
    .clk,
    .reset,
    .ctrl(vls_ctrl),
    .a(vls_in_d),
    //.a(vrf_out),
    .load_in,
    .y(vrf_in_from_vls),
    .store_serial_in,
    .store_serial_out
  );


  //--------------------------------------------------------------------------------
  // Vector compare unit
  //--------------------------------------------------------------------------------

  always_ff @(posedge clk) begin
  //always_latch begin
    if( ctrl.cmp_reg_in_en[0] )
      cmp_in_d <= vrf_out;
  end

  Vector_compare #(
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE)
  ) cmp (
    .clk,
    .reset,
    .ctrl(cmp_ctrl),
    .a(cmp_in_d),
    //.a(vrf_out),
    .vcr(vcr_out)
  );


  //--------------------------------------------------------------------------------
  // Vector parallel load/store unit
  //--------------------------------------------------------------------------------

  Vector_raw pls_in_d;

  always_ff @(posedge clk) begin
    if( ctrl.pls_reg_in_en[0] )
      pls_in_d <= vrf_out;
  end


  Vector_pls #(
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE)
  ) pls (
    .clk,
    .reset,
    .ctrl(pls_ctrl),
    .a(pls_in_d),
    .vcr(vcr),
    .y(vrf_in_from_pls),
    .write_mask(vrf_write_mask_from_pls),
    .sdata(sdata),
    .mdata(mdata),
    .mbyteen(mbyteen)
  );


  //--------------------------------------------------------------------------------
  // Permutation unit
  //--------------------------------------------------------------------------------

  always_ff @(posedge clk) begin
    if( ctrl.permute_reg_in_en[0] )
      permute_in_a_d <= vrf_out;
    if( ctrl.permute_reg_in_en[1] )
      permute_in_b_d <= vrf_out;
  end


  Vector_permute #(
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE)
  ) permute (
    .clk,
    .reset,
    .ctrl(permute_ctrl),
    .vcr(vcr),
    .a(permute_in_a_d),
    .b(permute_in_b_d),
    .y(vrf_in_from_permute)
  );


endmodule

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
