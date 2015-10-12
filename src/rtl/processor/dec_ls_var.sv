/** _use_m4_ macros
* include(ops.m4)
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


module Dec_ls_var
( input logic clk, reset,
  input Frontend::Issue_slot inst,
  Load_store_ctrl_if.decode ctrl );

import Pu_types::*;
import Pu_inst::*;

//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

logic en;
logic we;
Load_mode mode;
logic multiple;
logic first_cycle;
logic multiple_inc;
Inst ir;
logic return_dout;
logic return_addr;
logic return_addr_early;
logic exts;

assign ir = inst.ir;

//---------------------------------------------------------------------------
// Decoding logic
//---------------------------------------------------------------------------

//always_comb
//begin : set_enables
//// defaults
//en = 1'b0;

//unique case(ir.d.opcd)
  //Op_alu_xo: begin
    //unique case(ir.x.xo)
      //Xop_lwzx, Xop_lwzux,
      //Xop_lhzx, Xop_lhzux,
      //Xop_lbzx, Xop_lhzux,
      //Xop_stwx, Xop_stwux,
      //Xop_sthx, Xop_sthux,
      //Xop_stbx, Xop_stbux:
      //begin
        //en = 1'b1;
      //end

      //default: begin end
    //endcase
  //end
  
  //// load/store instructions
  //Op_lwz, Op_stw, Op_lbz, Op_stb, Op_lhz, Op_sth,
  //Op_stwu, Op_stbu, Op_sthu:
  //begin
    //en = 1'b1;
  //end

  //default: begin
  //end
//endcase
//end : set_enables


//---------------------------------------------------------------------------
// Control memory write
//---------------------------------------------------------------------------
always_comb
begin
logic[15:0] cop;

cop = {ir.x.opcd, ir.x.xo};
unique casez(cop)
  {Op_stw, 10'bzzzzzzzzzz}, {Op_sth, 10'bzzzzzzzzzz}, {Op_stb, 10'bzzzzzzzzzz},
  {Op_stwu, 10'bzzzzzzzzzz}, {Op_sthu, 10'bzzzzzzzzzz}, {Op_stbu, 10'bzzzzzzzzzz},
  {Op_alu_xo, Xop_stwx}, {Op_alu_xo, Xop_sthx},
  {Op_alu_xo, Xop_stbx},
  {Op_alu_xo, Xop_stwux}, {Op_alu_xo, Xop_sthux},
  {Op_alu_xo, Xop_stbux},
  OP(Op_stmw):
    we = 1'b1;

  default:
    we = 1'b0;
endcase
end

always_comb
begin : mem_write_mode
logic[15:0] cop;

cop = {ir.x.opcd, ir.x.xo};

unique casez(cop)
  {Op_stb, 10'bz}, {Op_lbz, 10'bz},
  {Op_stbu, 10'bz}, {Op_lbzu, 10'bz},
  {Op_alu_xo, Xop_lbzx}, {Op_alu_xo, Xop_stbx},
  {Op_alu_xo, Xop_lbzux}, {Op_alu_xo, Xop_stbux}:
    mode = Load_byte;

  {Op_sth, 10'bz}, {Op_lhz, 10'bz},
  {Op_sthu, 10'bz}, {Op_lhzu, 10'bz},
  {Op_alu_xo, Xop_lhzx}, {Op_alu_xo, Xop_sthx},
  {Op_alu_xo, Xop_lhzux}, {Op_alu_xo, Xop_sthux},
  {Op_lha, 10'bz}, {Op_alu_xo, Xop_lhax},
  {Op_lhau, 10'bz}, {Op_alu_xo, Xop_lhaux}:
    mode = Load_halfword;

  default:
    mode = Load_word;
endcase
end : mem_write_mode

//---------------------------------------------------------------------------
// Select output of load/store unit
//---------------------------------------------------------------------------

dnl // always_comb begin
dnl //   OPCMP(ir)
dnl //     STORE_UPDATE_OPS:
dnl //       return_dout = 1'b0;
dnl // 
dnl //     LOAD_UPDATE_OPS:
dnl //       return_dout = ~return_addr;
dnl // 
dnl //     default:
dnl //       return_dout = 1'b1;
dnl //   ENDOPCMP
dnl // end

assign return_dout = ~return_addr & ~return_addr_early;

always_ff @(posedge clk or posedge reset)
  if( reset )
    return_addr <= 1'b0;
  else begin
    if( inst.valid ) begin
      OPCMP(ir)
        LOAD_UPDATE_OPS:
          return_addr <= ~return_addr;

        default:
          return_addr <= 1'b0;
      ENDOPCMP
    end
  end

always_comb begin
  OPCMP(ir)
    STORE_UPDATE_OPS:
      return_addr_early = 1'b1;

    default:
      return_addr_early = 1'b0;
  ENDOPCMP
end

//---------------------------------------------------------------------------
// load halfword algebraic support
//---------------------------------------------------------------------------

dnl //always_ff @(posedge clk)
dnl //begin
dnl //OPCMP(ir)
dnl   //LOAD_ALGEBRAIC_OPS:
dnl     //exts <= 1'b1;
dnl 
dnl   //default:
dnl     //exts <= 1'b0;
dnl //ENDOPCMP
dnl //end
always_comb begin
  OPCMP(ir)
    LOAD_ALGEBRAIC_OPS:
      exts = 1'b1;

    default:
      exts = 1'b0;
  ENDOPCMP
end

//---------------------------------------------------------------------------
// Set load/store multiple control signals
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Output register
//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
if( reset ) begin
  ctrl.en_dec <= 1'b0;
  ctrl.we <= 1'b0;
  ctrl.mode <= Load_null;
  ctrl.multiple <= 1'b0;
  ctrl.first_cycle <= 1'b0;
  ctrl.multiple_inc <= 1'b0;
  ctrl.return_dout <= 1'b0;
  ctrl.exts <= 1'b0;
  ctrl.do_request <= 1'b0;
end else begin
  // default assignment
  ctrl.en_dec <= 1'b0;
  ctrl.we <= 1'b0;
  ctrl.mode <= Load_null;
  ctrl.multiple <= 1'b0;
  ctrl.first_cycle <= 1'b0;
  ctrl.multiple_inc <= 1'b0;
  ctrl.return_dout <= 1'b0;
  ctrl.exts <= 1'b0;
  ctrl.do_request <= 1'b0;

  if( inst.valid ) begin
    //ctrl.en_dec <= en;
    ctrl.en_dec <= 1'b1;
    ctrl.we <= we;
    ctrl.mode <= mode;
    //ctrl.multiple <= multiple;
    //ctrl.first_cycle <= first_cycle;
    //ctrl.multiple_inc <= multiple_inc;
    ctrl.return_dout <= return_dout;
    ctrl.exts <= exts;
    ctrl.do_request <= ~return_addr;
  end
end

`ifndef SYNTHESIS

  assert property(
    @(posedge clk) disable iff(reset)
    ( inst.valid |=> ctrl.en_dec )
  );

`endif /* SYNTHESIS */

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
