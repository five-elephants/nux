// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Dec_fixedpoint
  ( input logic clk, reset,
    input Frontend::Issue_slot inst,
    Fixedpoint_ctrl_if.decode ctrl );

  import Pu_types::*;
  import Pu_inst::*;


//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

Alu_op alu_op;
Cr_op cr_op;
Func_unit fxdp_sel;
logic[4:0] alu_crl_ba;
logic[4:0] alu_crl_bb;
logic[4:0] alu_crl_bt;
logic[7:0] src_cr;
Register_move reg_mv;
Inst ir;
logic oe;

assign ir = inst.ir;

//---------------------------------------------------------------------------
// Select ALU operation
//---------------------------------------------------------------------------
always_comb
begin
  unique case(ir.d.opcd)
    Op_subfic:
      alu_op = Alu_sub;

    Op_andi, Op_andis:
      alu_op = Alu_and;

    Op_ori, Op_oris:
      alu_op = Alu_or;

    Op_xori, Op_xoris:
      alu_op = Alu_xor;

    Op_rlwimi, Op_rlwinm, Op_rlwnm:
      alu_op = Alu_rotl;

    Op_cmpi:
      alu_op = Alu_cmp;

    Op_cmpli:
      alu_op = Alu_cmpl;

    Op_alu_xo: begin
      unique casez(ir.x.xo)
        {1'bz, Xop_add}, {1'bz, Xop_addc}, {1'bz, Xop_addme},
        {1'bz, Xop_addze}, {1'bz, Xop_adde}:
          alu_op = Alu_add;

        {1'bz, Xop_subf}, {1'bz, Xop_subfc}, {1'bz, Xop_subfme},
        {1'bz, Xop_subfze}, {1'bz, Xop_subfe}:
          alu_op = Alu_sub;

        Xop_cmp:            alu_op = Alu_cmp;
        Xop_cmpl:           alu_op = Alu_cmpl;
        {1'bz, Xop_neg}:    alu_op = Alu_neg;
        Xop_and:            alu_op = Alu_and;
        Xop_andc:           alu_op = Alu_andc;
        Xop_or:             alu_op = Alu_or;
        Xop_orc:            alu_op = Alu_orc;
        Xop_xor:            alu_op = Alu_xor;
        Xop_nand:           alu_op = Alu_nand;
        Xop_nor:            alu_op = Alu_nor;
        Xop_eqv:            alu_op = Alu_eqv;
        Xop_extsb:          alu_op = Alu_esb;
        Xop_extsh:          alu_op = Alu_esh;
        
        Xop_slw, Xop_srw, Xop_srawi, Xop_sraw:
                            alu_op = Alu_rotl;

        Xop_popcb:          alu_op = Alu_popcnt;
        Xop_prtyw:          alu_op = Alu_prty;
        Xop_cntlzw:         alu_op = Alu_cntlz;
        default:            alu_op = Alu_add;
      endcase
    end

    default:
      alu_op = Alu_add;
  endcase
end

//---------------------------------------------------------------------------
// control CR logic control signals
//---------------------------------------------------------------------------
assign alu_crl_ba = ir.xl.ba;
assign alu_crl_bb = ir.xl.bb;
assign alu_crl_bt = ir.xl.bt;

always_comb
begin
  // default assignment
  cr_op = Cr_and;

  if( ir.xl.opcd == Op_bclr ) begin
    unique case(ir.xl.xo)
      Xxop_crand:         cr_op = Cr_and;
      Xxop_crnand:        cr_op = Cr_nand;
      Xxop_cror:          cr_op = Cr_or;
      Xxop_crnor:         cr_op = Cr_nor;
      Xxop_crxor:         cr_op = Cr_xor;
      Xxop_creqv:         cr_op = Cr_eqv;
      Xxop_crandc:        cr_op = Cr_andc;
      Xxop_crorc:         cr_op = Cr_orc;
      default:            cr_op = Cr_and;
    endcase
  end
end

always_comb
  unique case(ir.xo.opcd)
    Op_alu_xo:
      oe = ir.xo.oe;

    Op_addic_rec:
      oe = 1'b0;

    default:
      oe = 1'b0;
  endcase

//---------------------------------------------------------------------------
// Control fixedpoint write back multiplexer
//---------------------------------------------------------------------------
always_comb
begin
  // default assignment
  fxdp_sel = Fu_alu;

  case(ir.d.opcd)  // TODO mul/div instructions
    Op_rlwimi, Op_rlwinm, Op_rlwnm:
      fxdp_sel = Fu_rotm;

    Op_alu_xo: begin
      case(ir.x.xo)
        Xop_slw, Xop_srw, Xop_srawi, Xop_sraw:
          fxdp_sel = Fu_rotm;

        Xop_mfspr, Xop_mfocrf, Xop_mtocrf, Xop_mfmsr, Xop_mtmsr,
        Xop_mtspr, Xop_mfspr:
          fxdp_sel = Fu_spreu;
      endcase
    end

    Op_bclr:
      fxdp_sel = Fu_spreu;
  endcase
end

always_comb
// This seems to be another ModelSim bug:
// Using always_comb the process is not always triggered at changes of spr
// Perhaps because of the indexing?
//always @(ir.d.opcd, ir.xl.xo, ir.xl.ba, ir.xfx.spr)
begin
  if( ir.d.opcd == Op_bclr && ir.xl.xo == Xxop_mcrf ) begin
    logic[2:0] ba;
    ba = ir.xl.ba[4:2];
    unique case(ba)
      3'b000:   src_cr = 8'b10000000;
      3'b001:   src_cr = 8'b01000000;
      3'b010:   src_cr = 8'b00100000;
      3'b011:   src_cr = 8'b00010000;
      3'b100:   src_cr = 8'b00001000;
      3'b101:   src_cr = 8'b00000100;
      3'b110:   src_cr = 8'b00000010;
      3'b111:   src_cr = 8'b00000001;
      //default:  src_cr = 8'b10000000;
      default:  src_cr = 8'bxxxxxxxx;
    endcase
  end else if( (ir.d.opcd == Op_alu_xo) && (ir.xfx.xo == Xop_mfocrf) 
      && (ir.xfx.spr[9] == 1'b0) ) 
  begin
    src_cr[7:0] = '1;
  end else begin
    src_cr[7:0] = ir.xfx.spr[8:1];
  end
end

always_comb
begin
  reg_mv = Rmv_none;

  if( ir.d.opcd == Op_alu_xo ) begin
    unique case(ir.xfx.xo)
      Xop_mtocrf:   reg_mv = Rmv_gtc;  
      Xop_mfocrf:   reg_mv = Rmv_ctg;  
      Xop_mtspr:    reg_mv = Rmv_gts;  
      Xop_mfspr:    reg_mv = Rmv_stg;  
      Xop_mtmsr:    reg_mv = Rmv_gtm;
      Xop_mfmsr:    reg_mv = Rmv_mtg;
      default:      reg_mv = Rmv_none; 
    endcase
  end else if( ir.d.opcd == Op_bclr ) begin
    if( ir.xl.xo == Xxop_mcrf ) 
      reg_mv = Rmv_ctc;
  end
end

//---------------------------------------------------------------------------
// Output register
//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    ctrl.alu_op <= Alu_andc;
    ctrl.cr_op <= Cr_and;
    ctrl.sel <= Fu_none;
    ctrl.crl_ba <= '0;
    ctrl.crl_bb <= '0;
    ctrl.crl_bt <= '0;
    ctrl.reg_mv <= Rmv_none;
    ctrl.src_cr <= '0;
    ctrl.oe <= 1'b0;
  end else begin
    //default assignment
    ctrl.alu_op <= Alu_andc;
    ctrl.cr_op <= Cr_and;
    ctrl.sel <= Fu_none;
    ctrl.crl_ba <= '0;
    ctrl.crl_bb <= '0;
    ctrl.crl_bt <= '0;
    ctrl.reg_mv <= Rmv_none;
    ctrl.src_cr <= '0;
    ctrl.oe <= 1'b0;

    if( inst.valid ) begin
      ctrl.alu_op <= alu_op;
      ctrl.cr_op <= cr_op;
      ctrl.sel <= fxdp_sel;
      ctrl.crl_ba <= alu_crl_ba;
      ctrl.crl_bb <= alu_crl_bb;
      ctrl.crl_bt <= alu_crl_bt;
      ctrl.reg_mv <= reg_mv;
      ctrl.src_cr <= src_cr;
      ctrl.oe <= oe;
    end
  end

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
