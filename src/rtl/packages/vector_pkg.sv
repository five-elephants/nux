// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


package Vector;

  typedef struct packed {
    logic[0:3] eq;
    logic[0:3] gt;
    logic[0:3] lt;
  } Compare;

  typedef logic[4:0] Vrf_index;

  typedef struct packed {
		Pu_inst::Fxv_opcd xo;
    Pu_inst::Fxv_cond cond;
    Vrf_index rt;
    Vrf_index ra;
    Vrf_index rb;
    Pu_types::Word g;
  } Vector_operation;

  typedef enum logic[2:0] {
    CMP_EQ = 3'b001,
    CMP_GT = 3'b010,
    CMP_LT = 3'b100
  } Vector_compare_mode;

  typedef enum logic[5:0] {
    PERMUTE_PACK   = 6'b00_0001,
    PERMUTE_SPLAT  = 6'b00_0010,
    PERMUTE_SPLATB = 6'b00_0100,
    PERMUTE_SHIFT  = 6'b00_1000,
    PERMUTE_SHIFTB = 6'b01_0000,
    PERMUTE_SELECT = 6'b10_0000
  } Permute_op;

  typedef logic[1:0] Permute_size;

	localparam int NUM_UNITS = 5;

  typedef enum logic[4:0] {
    VU_MADD    = 5'b0_0001,
    VU_CMP     = 5'b0_0010,
    VU_LS      = 5'b0_0100,
    VU_PLS     = 5'b0_1000,
    VU_PERMUTE = 5'b1_0000,
    VU_UNDEF   = 5'bx_xxxx
  } Unit;

  typedef enum logic[2:0] {
    VU_ID_MADD    = 3'b000,
    VU_ID_CMP     = 3'b001,
    VU_ID_LS      = 3'b010,
    VU_ID_PLS     = 3'b011,
    VU_ID_PERMUTE = 3'b100,
    VU_ID_UNDEF   = 3'bxxx
  } Unit_id;


  typedef struct packed {
    Unit_id unit;
    logic[3:0] entry;
  } Rs_ref;

  typedef struct {
    Vrf_index dest;
    Vrf_index src[0:1];
    Rs_ref src_ref[0:1];
    logic required[0:1];
    logic valid[0:1];
    logic write_dest;
    Pu_types::Word g;
    logic require_vcr;
    logic vcr_valid;
  } Operands;

  typedef logic[5:0] Readlock_ctr;
  localparam int READLOCK_MAX = 2 ** $bits(Readlock_ctr) - 1;


  function automatic Unit unit_id_to_unit(Unit_id id);
    unique case(id)
      VU_ID_MADD: return VU_MADD;
      VU_ID_CMP: return VU_CMP;
      VU_ID_LS: return VU_LS;
      VU_ID_PLS: return VU_PLS;
      VU_ID_PERMUTE: return VU_PERMUTE;
      default: return VU_UNDEF;
    endcase
  endfunction

endpackage


/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
