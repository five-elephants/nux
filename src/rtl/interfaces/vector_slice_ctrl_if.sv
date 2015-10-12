// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Vector_slice_ctrl_if
  #(parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int VRF_SIZE = 32)
  ();

  logic vrf_en;
  logic[$clog2(VRF_SIZE)-1:0] vrf_addr;
  logic vrf_we;
  logic valu_reg_in_en[0:1];
  Vector::Unit vrf_src_unit;

  logic vls_reg_in_en[0:0];

  logic cmp_reg_in_en[0:0];
  logic vcr_we;
  Vector::Vector_compare_mode vcr_enable_mode;

  logic pls_reg_in_en[0:0];

  logic permute_reg_in_en[0:1];

  modport ctrl (
    output vrf_en, vrf_addr, vrf_we, valu_reg_in_en,
      vrf_src_unit,
    output vls_reg_in_en,
    output cmp_reg_in_en, vcr_we, vcr_enable_mode,
    output pls_reg_in_en,
    output permute_reg_in_en
  );

  modport slice (
    input vrf_en, vrf_addr, vrf_we, valu_reg_in_en,
      vrf_src_unit,
    input vls_reg_in_en,
    input cmp_reg_in_en, vcr_we, vcr_enable_mode,
    input pls_reg_in_en,
    input permute_reg_in_en
  );

endinterface

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
