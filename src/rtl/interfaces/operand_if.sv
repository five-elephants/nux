// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Backend::*;
import Frontend::Thread_id;
import Pu_types::*;

/* m4 macros

changequote(<,>)

dnl define array accessor function.
define(<ACC_AR>, <dnl
  function automatic $1 get_$2_$3(input $4 sel);
    //return $2[sel].$3;
    unique case(sel)
      0: return $2_0.$3;
      default: return 'x;
    endcase
  endfunction
>)

changequote()

* */

interface Operand_if;
  Operands opbus_0;


//ACC_AR(Word, opbus, a, Thread_id)
//ACC_AR(Word, opbus, b, Thread_id)
//ACC_AR(Word, opbus, c, Thread_id)
//ACC_AR(logic, opbus, cin, Thread_id)
//ACC_AR(Cr_bits, opbus, cr, Thread_id)


  //function automatic void set_opbus(input Thread_id sel, Operands bus);
    ////opbus = bus;
    //unique case(sel)
      //0: opbus_0 = bus;
      //default: opbus_0 = operands_undef();
    //endcase
  //endfunction

  //function automatic Operands get_opbus(input Thread_id sel);
    //return opbus[sel];
  //endfunction

  //function automatic Operands get_opbus_a(input Thread_id sel);
    //return opbus[sel].a;
  //endfunction
  
  //modport write(import set_opbus);
  modport write(output opbus_0);
  //modport read(input opbus);
  //modport read(input opbus_0, import get_opbus_a, get_opbus_b, get_opbus_c, get_opbus_cin,
                      //get_opbus_cr );
  modport read(input opbus_0);
endinterface


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
