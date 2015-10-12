/* _use_m4_ macros
include(ops.m4)
* */

// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.




module Predecode
  #(parameter Pu_types::Opt_mem OPT_DMEM = Pu_types::MEM_TIGHT,
    parameter bit WITH_NEVER = 1'b0 )
  ( input logic clk, reset,
    input Frontend::Fetch_state fst,
    input Frontend::Seq_ctr seq_ctr,
    output Frontend::Predecoded predec );

import Pu_types::*;
import Pu_inst::*;
import Frontend::*;


/* m4 macros

changequote(<,>)

define(<DEF_FUN>, <dnl
function automatic $2 $1(input Fetch_state fst);
  $2 rv;
>)

define(<END_FUN>, <dnl
  return rv;
endfunction
>)

define(<DEF_FUN_CMP>, <dnl
DEF_FUN($1, $2)
  OPCMP(fst.inst)
    default:
      rv = $3;
>)

define(<END_FUN_CMP>, <
  ENDOPCMP
END_FUN
>)

define(<PD_MAP>, <always_comb predec.$1 = pd_$1(fst);>)

DEF_SEQ(<load_update>, 2)
  VAL(logic, write_ra, <1'b1, 1'b0>)
  VAL(logic, write_rt, <1'b0, 1'b1>)
END_SEQ()

changequote()

*/

//---------------------------------------------------------------------------
// Multi-cycle sequences
//---------------------------------------------------------------------------

/* load with update sequence */
localparam logic[0:1] seq_load_update_read_ra = { 1'b1, 1'b0 };
localparam logic[0:1] seq_load_update_indexed_read_rb = { 1'b1, 1'b0 };
localparam logic[0:1] seq_load_update_write_ra = { 1'b0, 1'b1 };
localparam logic[0:1] seq_load_update_write_rt = { 1'b1, 1'b0 };
localparam logic[0:1] seq_load_update_nd_latency = { 1'b1, 1'b0 };
//localparam logic[0:1] seq_load_update_nd_latency = { 1'b0, 1'b0 };  // oportunistic write-back
localparam Inst_latency[0:1] seq_load_update_latency_bus = { 4'd4, 4'd2 };


/* load/store multiple sequence */
localparam Reg_index[31:0] seq_mem_multiple_rt = {
  5'd31, 5'd30, 
  5'd29, 5'd28, 5'd27, 5'd26, 5'd25, 5'd24, 5'd23, 5'd22, 5'd21, 5'd20,
  5'd19, 5'd18, 5'd17, 5'd16, 5'd15, 5'd14, 5'd13, 5'd12, 5'd11, 5'd10,
   5'd9,  5'd8,  5'd7,  5'd6,  5'd5,  5'd4,  5'd3,  5'd2,  5'd1,  5'd0
};


//---------------------------------------------------------------------------
// Functions
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
function automatic logic[7:0] cr_idx_decode(input logic[2:0] idx);
  logic[7:0] rv;
  
  unique case(idx)
    3'd0:    rv = 8'b0000_0001;
    3'd1:    rv = 8'b0000_0010;
    3'd2:    rv = 8'b0000_0100;
    3'd3:    rv = 8'b0000_1000;
    3'd4:    rv = 8'b0001_0000;
    3'd5:    rv = 8'b0010_0000;
    3'd6:    rv = 8'b0100_0000;
    3'd7:    rv = 8'b1000_0000;
    default: rv = 8'bxxxx_xxxx;
  endcase

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic Fu_set pd_fu_set(input Fetch_state fst);
  Fu_set rv;

  OPCMP(fst.inst)
    BRANCH_OPS, TRAP_OPS: 
      rv = FUB_BRANCH;

    LOAD_OPS, STORE_OPS, OP(Op_lmw), OP(Op_stmw): 
      rv = FUB_LOAD_STORE;

    MUL_OPS:
      rv = FUB_MUL_DIV;
    
    DIV_OPS:
      rv = FUB_DIV;

    DEV_CTRL_OPS:
      rv = FUB_IO;

    VECTOR_OPS:
      rv = FUB_VECTOR;

    NEVER_OPS:  // XXX this could be left out if NEVER is not used
      rv = FUB_NEVER;

    SYNAPSE_OPS:
      rv = FUB_SYNAPSE;

    default:
      rv = FUB_FIXEDPOINT;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
DEF_FUN_CMP(pd_context_sync, logic, 1'b0)
  OPX(Xop_sync), OPX(Xop_mtmsr), TRAP_OPS:
    rv = 1'b1;
END_FUN_CMP
//---------------------------------------------------------------------------
function automatic logic pd_halt(input Fetch_state fst);
  logic rv;

  if( (fst.inst.x.opcd == Op_alu_xo)
      && (fst.inst.x.xo == Xop_wait)
      && (fst.inst.x.rt[1:0] == 2'b00) )
    rv = 1'b1;
  else
    rv = 1'b0;

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_write_ra(input Fetch_state fst);
  logic rv;

  OPCMP(fst.inst)
    STORE_UPDATE_OPS, OPX(Xop_mfspr), OPX(Xop_mfocrf):
      rv = 1'b1;

    LOAD_UPDATE_OPS:
      rv = seq_load_update_write_ra[seq_ctr];
      //rv = SEQ(`load_update', `seq_ctr', `write_ra');
      // # -> rv = seq_load_update_write_ra[seq_ctr];

    default:
      rv = 1'b0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_write_rt(input Fetch_state fst);
  logic rv;
  
  OPCMP(fst.inst)
    ROTATE_OPS, LOGICAL_OPS,
    ADDSUB_OPS, LOAD_NOUPDATE_OPS, MUL_OPS,
    OP(Op_lmw), OPXO(Xop_neg), OPX(Xop_mfmsr):
      rv = 1'b1;

    DIV_OPS:
      //rv = seq_div_write_rt[seq_ctr];
      rv = 1'b1;

    LOAD_UPDATE_OPS:
      rv = seq_load_update_write_rt[seq_ctr];

    OPX(Xop_eciwx):
      rv = 1'b1;

    OPX2(Op_nve_xo, Xop_nvem), OPX2(Op_nve_xo, Xop_nves):
      rv = 1'b1;

    OPNVE(Xop_synmfvr), OPNVE(Xop_synmfp):
      rv = 1'b1;

    default:
      rv = 1'b0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_read_ra(input Fetch_state fst);
  logic rv;

  OPCMP(fst.inst)
    STORE_IMMEDIATE_OPS, STORE_INDEXED_OPS, LOAD_NOUPDATE_OPS,
    OP(Op_lmw), OP(Op_stmw),
    OP(Op_addi), OP(Op_addis),
    VECTOR_STORE_OPS, VECTOR_LOAD_OPS,
    OPFXV(Xop_fxvlax), OPFXV(Xop_fxvstax), OPFXV(Xop_fxvinx), OPFXV(Xop_fxvoutx),
    OPFXV(Xop_fxvsplath), OPFXV(Xop_fxvsplatb):
      rv = (fst.inst.x.ra != 0);  // only read when RA != 0
    
    ADDSUB_REG_OPS, OPXO(Xop_neg), 
    OP(Op_addic), OP(Op_addic_rec), OP(Op_subfic),
    MUL_OPS,
    LOGICAL_OPS, COMPARE_OPS, TRAP_OPS, ROTATE_OPS,
    OPX(Xop_mtspr), OPX(Xop_mtocrf),
    DEV_CTRL_OPS:
      rv = 1'b1;

    DIV_OPS:
      //rv = seq_div_read_ra[seq_ctr];
      rv = 1'b1;

    LOAD_UPDATE_OPS:
      rv = seq_load_update_read_ra[seq_ctr];

    NEVER_OPS:
      rv = 1'b1;

    OPNVE(Xop_synmtl), OPNVE(Xop_synmtvr), OPNVE(Xop_synops), OPNVE(Xop_synmtp):
      rv = 1'b1;

    default:
      rv = 1'b0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_read_rb(input Fetch_state fst);
  logic rv;

  OPCMP(fst.inst)
    STORE_INDEXED_OPS, ADDSUB_REG_OPS, 
    OPX(Xop_lwzx), OPX(Xop_lhzx), OPX(Xop_lhax), OPX(Xop_lbzx),
    MUL_REG_OPS,
    OPX(Xop_cmp), OPX(Xop_cmpl),
    ROTATE_REG_OPS, TRAP_REG_OPS, LOGICAL_REG_OPS,
    DEV_CTRL_OPS,
    VECTOR_LOAD_OPS, VECTOR_STORE_OPS,
    OPFXV(Xop_fxvlax), OPFXV(Xop_fxvstax), OPFXV(Xop_fxvinx), OPFXV(Xop_fxvoutx):
      rv = 1'b1;

    OPX(Xop_lwzux), OPX(Xop_lhzux), OPX(Xop_lbzux), OPX(Xop_lhaux):
      rv = seq_load_update_indexed_read_rb[seq_ctr];

    DIV_OPS:
      //rv = seq_div_read_rb[seq_ctr];
      rv = 1'b1;

    OPX2(Op_nve_xo, Xop_nves), OPX2(Op_nve_xo, Xop_nvemtl):
      rv = 1'b1;

    OPNVE(Xop_synmtl), OPNVE(Xop_synops):
      rv = 1'b1;

    default:
      rv = 1'b0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_read_rt(input Fetch_state fst);
  logic rv;

  OPCMP(fst.inst)
    STORE_OPS, OP(Op_stmw),
    OPX(Xop_mfocrf),                // This dependency is not required for PowerISA
                                    // compliance, but the testbench prediction
                                    // assumes this.
    OP(Op_rlwimi), OPX(Xop_mtmsr),
    OPX(Xop_ecowx):
      rv = 1'b1;

    OPNVE(Xop_synops):
      rv = 1'b1;

    default:
      rv = 1'b0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic Reg_index pd_ra(input Fetch_state fst);
  Reg_index rv;

  OPCMP(fst.inst)
    LOGICAL_OPS, ROTATE_OPS, MOVE_WITH_SYSTEM_REG_OPS:
      rv = fst.inst.x.rt;

    default:
      rv = fst.inst.x.ra;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic Reg_index pd_rb(input Fetch_state fst);
  Reg_index rv;

  OPCMP(fst.inst)
    default:
      rv = fst.inst.x.rb;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic Reg_index pd_rt(input Fetch_state fst);
  Reg_index rv;

  OPCMP(fst.inst)
    LOGICAL_OPS, ROTATE_OPS: 
      rv = fst.inst.x.ra;

    OP(Op_lmw), OP(Op_stmw):
      rv = seq_mem_multiple_rt[fst.inst.d.rt + seq_ctr];

    default:
      rv = fst.inst.x.rt;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_b_immediate(input Fetch_state fst);
  logic rv;

  OPCMP(fst.inst)
    LOAD_IMMEDIATE_OPS, STORE_IMMEDIATE_OPS, COMPARE_IMMEDIATE_OPS, 
    ADDSUB_IMMEDIATE_OPS, MUL_IMMEDIATE_OPS, LOGICAL_IMMEDIATE_OPS,
    TRAP_IMMEDIATE_OPS, OP(Op_lmw), OP(Op_stmw),
    OP(Op_branch), OP(Op_bc), OP(Op_nvecmpi), OP(Op_syncmpi), OP(Op_syncmpi_rec):
      rv = 1'b1;

    default:
      rv = 1'b0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_read_lnk(input Fetch_state fst);
  logic rv;

  if( (fst.inst.xl.opcd == Op_bclr && fst.inst.xl.xo == Xxop_bclr)
    || (fst.inst.xfx.opcd == Op_alu_xo && fst.inst.xfx.xo == Xop_mfspr
        && fst.inst.xfx.spr == Spr_lnk) )
    rv = 1'b1;
  else
    rv = 1'b0;

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_write_lnk(input Fetch_state fst);
  logic rv;
  logic[15:0] cop;

  rv = 1'b0;

  cop = {fst.inst.xl.opcd, fst.inst.xl.xo};
  casez(cop)
    {Op_branch, 10'bzzzzzzzzzz},
    {Op_bc,     10'bzzzzzzzzzz},
    {Op_bclr,   Xxop_bclr},
    {Op_bclr,   Xxop_bcctr}:
    begin
      rv = fst.inst.xl.lk;
    end

    {Op_alu_xo, Xop_mtspr}:
      if( fst.inst.xfx.spr == Spr_lnk )
        rv = 1'b1;

    {Op_bclr, Xxop_rfi}, {Op_bclr, Xxop_rfci},
    {Op_bclr, Xxop_rfmci}:
      rv = 1'b0;
  endcase

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_read_ctr(input Fetch_state fst);
  logic rv;
  logic[15:0] cop;

  rv = 1'b0;

  cop = { fst.inst.xl.opcd, fst.inst.xl.xo };
  casez(cop)
    {Op_bc, 10'bzzzzzzzzzz}:
      if( fst.inst.b.bo[2] == 1'b0 ) begin
        rv = 1'b1;
      end

    {Op_bclr, Xxop_bclr}:
      if( fst.inst.b.bo[2] == 1'b0 )
      begin
        rv = 1'b1;
      end

    {Op_bclr, Xxop_bcctr}:
      rv = 1'b1;

    {Op_alu_xo, Xop_mfspr}:
      if( fst.inst.xfx.spr == Spr_ctr )
        rv = 1'b1;
  endcase

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_write_ctr(input Fetch_state fst);
  logic rv;
  logic[15:0] cop;

  rv = 1'b0;

  cop = { fst.inst.xl.opcd, fst.inst.xl.xo };
  casez(cop)
    {Op_bc, 10'bzzzzzzzzzz}:
      if( fst.inst.b.bo[2] == 1'b0 ) begin
        rv = 1'b1;
      end

    {Op_bclr, Xxop_bclr}:
      if( fst.inst.b.bo[2] == 1'b0 )
      begin
        rv = 1'b1;
      end

    {Op_alu_xo, Xop_mtspr}:
      if( fst.inst.xfx.spr == Spr_ctr )
        rv = 1'b1;
  endcase

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic Inst_latency pd_latency(input Fetch_state fst);
  Inst_latency rv;

  OPCMP(fst.inst)
    MUL_OPS:
      rv = mul_latency;

    DIV_OPS:
      rv = 1;

    STORE_UPDATE_OPS:
      if( OPT_DMEM == MEM_BUS )
        rv = ls_bus_addr_latency;
      else
        rv = ls_latency;

    LOAD_UPDATE_OPS:
      if( OPT_DMEM == MEM_BUS )
        rv = seq_load_update_latency_bus[seq_ctr];
      else
        rv = ls_latency;

    LOAD_NOUPDATE_OPS, STORE_NOUPDATE_OPS, OP(Op_lmw), OP(Op_stmw):
      if( OPT_DMEM == MEM_BUS )
        rv = ls_bus_latency;
      else
        rv = ls_latency;

    BRANCH_OPS:
      rv = branch_latency;

    DEV_CTRL_OPS:
      rv = dev_ctrl_latency;

    NEVER_OPS:
      rv = never_latency;

    SYNAPSE_DETERMINISTIC_OPS:
      rv = synapse_latency;

    default:
      rv = default_latency;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
DEF_FUN_CMP(pd_nd_latency, logic, 1'b0)
  LOAD_UPDATE_OPS:
    if( OPT_DMEM == MEM_BUS )
      rv = seq_load_update_nd_latency[seq_ctr];
    else
      rv = 1'b0;

  LOAD_NOUPDATE_OPS:
    if( OPT_DMEM == MEM_BUS )
      rv = 1'b1;
      //rv = 1'b0;  // oportunistic write-back
    else
      rv = 1'b0;

  DEV_CTRL_OPS:
    //rv = 1'b0;  // oportunistic write-back
    rv = 1'b1;

  SYNAPSE_ND_OPS:
    rv = 1'b1;
END_FUN_CMP
//---------------------------------------------------------------------------
function automatic logic[7:0] pd_write_cr(input Fetch_state fst);
  logic[7:0] rv;

  unique case(fst.inst.d.opcd)
    Op_andi, Op_andis, Op_addic_rec, Op_syncmpi_rec:
      rv = 8'h01;

    Op_cmpi, Op_cmpli: begin
      rv = 8'h00;
      rv[fst.inst.d.rt[4:2]] = 1'b1;
    end

    Op_rlwimi, Op_rlwinm, Op_rlwnm:
      rv = {7'h00, fst.inst.m.rc};

    Op_alu_xo: begin
      unique case(fst.inst.x.xo)
        Xop_cmp, Xop_cmpl: begin
          rv = 8'h00;
          rv[fst.inst.x.rt[4:2]] = 1'b1;
        end

        Xop_popcb, Xop_prtyw, Xop_mfocrf, Xop_wait,
        Xop_mtmsr, Xop_mfmsr, Xop_tw:
          rv = 8'h00;

        Xop_mtocrf: begin
          for(int i=0; i<8; i++)
            rv[i] = fst.inst.xfx.spr[8-i];
        end

        Xop_lwzx, Xop_lhzx, Xop_lbzx,
        Xop_lwzux, Xop_lhzux, Xop_lbzux,
        Xop_lhax, Xop_lhaux,
        Xop_stwx, Xop_sthx, Xop_stbx,
        Xop_stwux, Xop_sthux, Xop_stbux,
        Xop_eciwx, Xop_ecowx:
          rv = 8'b0;

        default:
          rv = {7'h00, fst.inst.xo.rc};
      endcase
    end

    Op_bclr: begin
      rv = 8'h00;

      unique case(fst.inst.xl.xo)
        Xxop_crand, Xxop_crnand, Xxop_cror, Xxop_cror, Xxop_crnor,
        Xxop_crxor, Xxop_creqv, Xxop_crorc, Xxop_crandc, Xxop_mcrf:
          rv[fst.inst.xl.bt[4:2]] = 1'b1;

        default:
          rv = 8'h00;
      endcase
    end

    default:
      rv = 8'h00;
  endcase

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic[7:0] pd_read_cr_0(input Fetch_state fst);
  logic[7:0] rv;

  rv = '0;

  unique case(fst.inst.d.opcd)
    Op_bc: begin
      // conditional branch reads CR, when the mask bit is not set
      if( fst.inst.b.bo[4] == 1'b0 ) 
        rv = cr_idx_decode(fst.inst.b.bi[4:2]);
    end

    Op_bclr: begin
      unique case(fst.inst.xl.xo)
        Xxop_bclr, Xxop_bcctr: begin
          if( fst.inst.b.bo[4] == 1'b0 ) 
            rv = cr_idx_decode(fst.inst.b.bi[4:2]);
        end

        Xxop_crand, Xxop_crnand, Xxop_cror, Xxop_cror, Xxop_crnor,
        Xxop_crxor, Xxop_creqv, Xxop_crorc, Xxop_crandc:
        begin
          rv = cr_idx_decode(fst.inst.xl.ba[4:2]);
        end

        Xxop_mcrf: begin
          rv = cr_idx_decode(fst.inst.xl.ba[4:2]);
        end

        default:
          rv = '0;
      endcase
    end

    Op_alu_xo: begin
      if( fst.inst.xfx.xo == Xop_mfocrf ) begin
        if( fst.inst.xfx.spr[9] == 1'b1 ) begin : mfocrf_form
          for(int i=0; i<8; i++)
            rv[i] = fst.inst.xfx.spr[8-i];
        end else begin : mfcr_form
          rv = '1;
        end
      end
    end

    default: begin
    end
  endcase

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic[7:0] pd_read_cr_1(input Fetch_state fst);
  logic[7:0] rv;

  OPCMP(fst.inst)
    CR_LOGICAL_OPS:
      rv = cr_idx_decode(fst.inst.xl.bb[4:2]);

    default:
      rv = '0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic[7:0] pd_read_cr_2(input Fetch_state fst);
  logic[7:0] rv;

  OPCMP(fst.inst)
    CR_LOGICAL_OPS:
      rv = cr_idx_decode(fst.inst.xl.bt[4:2]);

    default:
      rv = '0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_read_xer(input Fetch_state fst);
  logic rv;

  logic[14:0] cop;
  cop = {fst.inst.xo.opcd, fst.inst.xo.xo};

  rv = 1'b0;

  if( fst.inst.xo.opcd == Op_alu_xo && fst.inst.xfx.xo == Xop_mfspr
    && fst.inst.xfx.spr == Spr_xer )
    rv = 1'b1;
  else if( fst.inst.xo.opcd == Op_alu_xo )
    case(fst.inst.xo.xo)
      Xop_addme, Xop_addze, Xop_subfe, Xop_subfme,
      Xop_subfze, Xop_adde:
        rv = 1'b1;

      default:
        rv = fst.inst.xo.rc;
    endcase
  else 
    case(fst.inst.xo.opcd)
      Op_rlwimi, Op_rlwinm, Op_rlwnm, Op_cmpli, Op_cmpi:
        rv = fst.inst.xo.rc;  // same as fst.inst.m.rc

      default:
        rv = 1'b0;
    endcase


  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_write_xer(input Fetch_state fst);
  logic rv;
  logic record_ca;
  logic record_ov;
  logic write_xer;
  logic[15:0] cop;

  cop = {fst.inst.xo.opcd, fst.inst.x.xo};
  unique casez(cop)
    {Op_subfic, 10'bz}:              record_ca = 1'b1;
    {Op_addic, 10'bz}:               record_ca = 1'b1;
    {Op_addic_rec, 10'bz}:           record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_addc}:     record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_subfc}:    record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_adde}:     record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_addme}:    record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_addze}:    record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_subfe}:    record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_subfze}:   record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_subfme}:   record_ca = 1'b1;

    {Op_alu_xo, Xop_srawi},
    {Op_alu_xo, Xop_sraw}:           record_ca = 1'b1;
    default:                         record_ca = 1'b0;
  endcase

	unique case(fst.inst.d.opcd)
		Op_alu_xo: begin
			unique casez(fst.inst.x.xo)
				Xop_and, Xop_andc, Xop_or, Xop_orc, Xop_xor, 
				Xop_nand, Xop_nor, Xop_xor, Xop_eqv, Xop_extsb, Xop_extsh,
				Xop_slw, Xop_srw, Xop_srawi, Xop_sraw,
				Xop_lwzx, Xop_lhzx, Xop_lbzx,
				Xop_stwx, Xop_sthx, Xop_stbx,
				Xop_stwux, Xop_sthux, Xop_stbx, Xop_wait,
        {1'bz, Xop_mulhw}, {1'bz, Xop_mulhwu}:
				          record_ov = 1'b0;
				default:  record_ov = fst.inst.xo.oe;
			endcase
		end

		default:       record_ov = 1'b0;
	endcase

	if( fst.inst.d.opcd == Op_alu_xo 
			&& fst.inst.xfx.xo == Xop_mtspr
			&& fst.inst.xfx.spr == Spr_xer )
		write_xer = 1'b1;
	else
		write_xer = 1'b0;


  rv = record_ca | record_ov | write_xer;

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic Xer_dest pd_xer_dest(input Fetch_state fst);
  Xer_dest rv;

  /*OPCMP(fst.inst)
    OP(Op_subfic), OP(Op_addic), OP(Op_addic_rec),
    OPXO(Xop_addc),     
    OPXO(Xop_subfc),    
    OPXO(Xop_adde),     
    OPXO(Xop_addme),    
    OPXO(Xop_addze),    
    OPXO(Xop_subfe),    
    OPXO(Xop_subfze),   
    OPXO(Xop_subfme),   
    OPX(Xop_srawi),
    OPX(Xop_sraw):
      rv = XER_DEST_CA;

    OPX(Xop_mtspr):
        rv = XER_DEST_ALL;

    default:
      rv = XER_DEST_OV;
  ENDOPCMP*/
  logic record_ca;
  logic record_ov;
  logic write_xer;
  logic[15:0] cop;

  cop = {fst.inst.xo.opcd, fst.inst.x.xo};
  unique casez(cop)
    {Op_subfic, 10'bz}:              record_ca = 1'b1;
    {Op_addic, 10'bz}:               record_ca = 1'b1;
    {Op_addic_rec, 10'bz}:           record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_addc}:     record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_subfc}:    record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_adde}:     record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_addme}:    record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_addze}:    record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_subfe}:    record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_subfze}:   record_ca = 1'b1;
    {Op_alu_xo, 1'bz, Xop_subfme}:   record_ca = 1'b1;

    {Op_alu_xo, Xop_srawi},
    {Op_alu_xo, Xop_sraw}:           record_ca = 1'b1;
    default:                         record_ca = 1'b0;
  endcase

	unique case(fst.inst.d.opcd)
		Op_alu_xo: begin
			unique case(fst.inst.x.xo)
				Xop_and, Xop_andc, Xop_or, Xop_orc, Xop_xor, 
				Xop_nand, Xop_nor, Xop_xor, Xop_eqv, Xop_extsb, Xop_extsh,
				Xop_slw, Xop_srw, Xop_srawi, Xop_sraw,
				Xop_lwzx, Xop_lhzx, Xop_lbzx,
				Xop_stwx, Xop_sthx, Xop_stbx,
				Xop_stwux, Xop_sthux, Xop_stbx, Xop_wait:
				          record_ov = 1'b0;
				default:  record_ov = fst.inst.xo.oe;
			endcase
		end

		default:       record_ov = 1'b0;
	endcase

	if( fst.inst.d.opcd == Op_alu_xo 
			&& fst.inst.xfx.xo == Xop_mtspr
			&& fst.inst.xfx.spr == Spr_xer )
		write_xer = 1'b1;
	else
		write_xer = 1'b0;


  if( record_ca && record_ov )
    rv = XER_DEST_CA_OV;
  else if( record_ca && !record_ov )
    rv = XER_DEST_CA;
  else if( !record_ca && record_ov )
    rv = XER_DEST_OV;
  else if( write_xer )
    rv = XER_DEST_ALL;
  else
    rv = XER_ZERO;

  return rv;
endfunction
//---------------------------------------------------------------------------
DEF_FUN(pd_read_spr, logic)
  // default assignment
  rv = 1'b0;

  if( fst.inst.xfx.opcd == Op_alu_xo && fst.inst.xfx.xo == Xop_mfspr )
  begin
    rv = 1'b1;
  end else if( fst.inst.xl.opcd == Op_bclr && (fst.inst.xl.xo == Xxop_rfi 
      || fst.inst.xl.xo == Xxop_rfci
      || fst.inst.xl.xo == Xxop_rfmci) )
  begin
    rv = 1'b1;
  end
END_FUN
//---------------------------------------------------------------------------
DEF_FUN(pd_read_spr2, logic)
  // default assignment
  rv = 1'b0;

  if( fst.inst.xl.opcd == Op_bclr && (fst.inst.xl.xo == Xxop_rfi 
      || fst.inst.xl.xo == Xxop_rfci
      || fst.inst.xl.xo == Xxop_rfmci) )
  begin
    rv = 1'b1;
  end
END_FUN
//---------------------------------------------------------------------------
DEF_FUN(pd_spr, Spr_reduced)
  if( fst.inst.xl.opcd == Op_bclr )
    unique case(fst.inst.xl.xo)
      Xxop_rfi: begin
        rv = Spr_srr0;
      end

      Xxop_rfci: begin
        rv = Spr_csrr0;
      end

      Xxop_rfmci: begin
        rv = Spr_mcsrr0;
      end

      default: begin
        rv = Spr_srr0;
      end
    endcase
  else begin
    rv = Spr_reduced'(fst.inst.xfx.spr);
  end
END_FUN
//---------------------------------------------------------------------------
DEF_FUN(pd_spr2, Spr_reduced)
  if( fst.inst.xl.opcd == Op_bclr )
    unique case(fst.inst.xl.xo)
      Xxop_rfi: begin
        rv = Spr_srr1;
      end

      Xxop_rfci: begin
        rv = Spr_csrr1;
      end

      Xxop_rfmci: begin
        rv = Spr_mcsrr1;
      end

      default: begin
        rv = Spr_srr1;
      end
    endcase
  else begin
    rv = Spr_srr1;
  end
END_FUN
//---------------------------------------------------------------------------
DEF_FUN(pd_write_spr, logic)
	if( fst.inst.d.opcd == Op_alu_xo && fst.inst.xfx.xo == Xop_mtspr ) begin
		rv = 1'b1;
	end else begin
		rv = 1'b0;
	end
END_FUN
//---------------------------------------------------------------------------
DEF_FUN(pd_spr_dest, Spr_reduced)
  rv = Spr_reduced'(fst.inst.xfx.spr);
END_FUN
//---------------------------------------------------------------------------
DEF_FUN_CMP(pd_write_mem, logic, 1'b0)
  STORE_OPS:
    if( OPT_DMEM == Pu_types::MEM_TIGHT )
      rv = 1'b1;
    else
      rv = 1'b0;  // write accesses are directly tracked from the store queue
END_FUN_CMP
//---------------------------------------------------------------------------
DEF_FUN_CMP(pd_write_msr, logic, 1'b0)
  OPX(Xop_mtmsr):
    rv = 1'b1;
END_FUN_CMP
//---------------------------------------------------------------------------
DEF_FUN_CMP(pd_read_msr, logic, 1'b0)
  OPX(Xop_mfmsr):
    rv = 1'b1;
END_FUN_CMP
//---------------------------------------------------------------------------
DEF_FUN_CMP(pd_write_nve, logic, 1'b0)
  NEVER_OPS:
    rv = 1'b1;
END_FUN_CMP
//---------------------------------------------------------------------------
function automatic Seq_ctr pd_multicycles(input Fetch_state fst);
  Seq_ctr rv;

  OPCMP(fst.inst)
    LOAD_UPDATE_OPS:
      rv = 1;

    OP(Op_lmw), OP(Op_stmw):
      rv = 31 - fst.inst.d.rt;

    DIV_OPS:
      //rv = 24;
      rv = Frontend::div_latency - 4;

    default:
      rv = 0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_is_multicycle(input Fetch_state fst);
  logic rv;
    
  OPCMP(fst.inst)
    LOAD_UPDATE_OPS:
      rv = 1'b1;

    OP(Op_lmw), OP(Op_stmw):
      if( fst.inst.d.rt == 31 )
        rv = 1'b0;
      else
        rv = 1'b1;

    DIV_OPS:
      rv = 1'b0;

    default:
      rv = 1'b0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
function automatic logic pd_is_branch(input Fetch_state fst);
  logic rv;

  OPCMP(fst.inst)
    BRANCH_OPS:
      rv = 1'b1;

    default:
      rv = 1'b0;
  ENDOPCMP

  return rv;
endfunction
//---------------------------------------------------------------------------
DEF_FUN_CMP(pd_is_nop, logic, 1'b0)
  OP(Op_ori): 
    if( (fst.inst.d.rt == 0) && (fst.inst.d.ra == 0) && (fst.inst.d.d == 0) )
      rv = 1'b1;
    else
      rv = 1'b0;

  OPX(Xop_sync):
    rv = 1'b1;
END_FUN_CMP
//---------------------------------------------------------------------------
DEF_FUN_CMP(pd_mem_bar, logic, 1'b0)
  dnl OPNVE(Xop_synops), OPNVE(Xop_synswp):
  OPNVE(Xop_synswp):
    rv = 1'b1;
END_FUN_CMP
//---------------------------------------------------------------------------
DEF_FUN_CMP(pd_synops, logic, 1'b0)
  OPNVE(Xop_synops):
    rv = 1'b1;
END_FUN_CMP
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Decoding logic
//---------------------------------------------------------------------------
//assign predec.write_ra = pd_write_ra(fst);
PD_MAP(write_ra)
PD_MAP(write_rt)
PD_MAP(read_ra)
PD_MAP(read_rb)
PD_MAP(read_rt)
PD_MAP(ra)
PD_MAP(rb)
PD_MAP(rt)
PD_MAP(b_immediate)
PD_MAP(read_lnk)
PD_MAP(write_lnk)
PD_MAP(read_ctr)
PD_MAP(write_ctr)
PD_MAP(write_cr)
PD_MAP(read_cr_0)
PD_MAP(read_cr_1)
PD_MAP(read_cr_2)
PD_MAP(read_xer)
PD_MAP(write_xer)
PD_MAP(xer_dest)
PD_MAP(fu_set)
PD_MAP(halt)
PD_MAP(context_sync)
PD_MAP(latency)
PD_MAP(nd_latency)
PD_MAP(multicycles)
PD_MAP(is_multicycle)
PD_MAP(is_branch)
PD_MAP(read_spr)
PD_MAP(read_spr2)
PD_MAP(spr)
PD_MAP(spr2)
PD_MAP(write_spr)
PD_MAP(spr_dest)
PD_MAP(write_mem)
PD_MAP(write_msr)
PD_MAP(write_nve)
PD_MAP(read_msr)
PD_MAP(is_nop)
PD_MAP(mem_bar)
PD_MAP(synops)

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
