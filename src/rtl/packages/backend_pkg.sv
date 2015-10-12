// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


package Backend;
  /** Bundles all signals that are fetched by operand fetch. */
  typedef struct {
    Pu_types::Word a;
    Pu_types::Word b;
    Pu_types::Word c;
    logic cin;
    logic so;  // SO field from XER
    //Cr_field crf;
    //Condition_register cr;
    Pu_types::Cr_bits cr;
  } Operands;

  typedef Operands Operand_bus[0:Frontend::num_threads-1];

  //const Operands operands_undef = { 32'bx, 32'bx, 32'bx, 1'bx, 32'bx };

  /** Bundles all result signals from functional units. */
  typedef struct {
    Pu_types::Word res_a;
    Pu_types::Word res_b;
    logic cout;
    logic ov;
    Pu_types::Cr_field crf;
    Pu_types::Msr msr;
    logic valid;
  } Result_bus;

  typedef Result_bus Result_bus_array[0:Frontend::num_fubs-1];

  //const Result_bus result_bus_undef = { 32'bx, 32'bx, 1'bx, 4'bx, 32'bx };

  //---------------------------------------------------------------------------
  function automatic Operands operands_undef();
    //Operands rv;

    //rv.a = 'x;
    //rv.b = 'x;
    //rv.c = 'x;
    //rv.cin = 'x;
    //rv.cr = 'x;

    //return rv;
    operands_undef.a = 'x;
    operands_undef.b = 'x;
    operands_undef.c = 'x;
    operands_undef.cin = 'x;
    operands_undef.cr = 'x;
  endfunction
  //---------------------------------------------------------------------------
  function automatic Result_bus result_bus_undef();
    //Result_bus rv;

    //rv.res_a = 'x;
    //rv.res_b = 'x;
    //rv.cout = 'x;
    //rv.crf = 'x;
    //rv.msr = 'x;
    
    //return rv;
    result_bus_undef.res_a = 'x;
    result_bus_undef.res_b = 'x;
    result_bus_undef.cout = 'x;
    result_bus_undef.crf = 'x;
    result_bus_undef.msr = 'x;
  endfunction
  //---------------------------------------------------------------------------
endpackage

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
