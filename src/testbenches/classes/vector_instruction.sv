// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef VECTOR_INSTRUCTION__
`define VECTOR_INSTRUCTION__

`include "instruction.sv"

class Vector_instruction extends Instruction;
  rand Opcd opcd;
  rand logic[4:0] rt;
  rand logic[4:0] ra;
  rand logic[4:0] rb;
  rand Pu_inst::Fxv_opcd xo;
  rand Pu_inst::Fxv_cond cond;


  constraint valid_opcodes {
    (opcd == Pu_inst::Op_nve_xo) && (xo != Xop_fxv_null);
  }

  //constraint force_regs {
    //rt == 0 && ra == 0 && rb == 1;
  //}

  //constraint force_cond {
    //cond == Pu_inst::Fxv_cond_null;
  //}


  function new (Opcd opcd = Op_nve_xo,
      int rt = 0,
      int ra = 0,
      int rb = 0,
      Pu_inst::Fxv_opcd xo = Xop_fxvmahm,
      Pu_inst::Fxv_cond cond = Pu_inst::Fxv_cond_null);
    this.opcd = opcd;
    this.rt = rt;
    this.ra = ra;
    this.rb = rb;
    this.xo = xo;
    this.cond = cond;
  endfunction

  /**
   * Generate a 32-bit instruction word from the class contents.
   */
  virtual function Inst get();
    Inst rv;
    rv.fxv.opcd = opcd;
    rv.fxv.rt = rt;
    rv.fxv.ra = ra;
    rv.fxv.rb = rb;
    rv.fxv.xo = xo;
    rv.fxv.cond = cond;

    return rv;
  endfunction
endclass

`endif


/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
