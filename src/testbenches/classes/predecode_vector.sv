// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef PREDECODE_VECTOR__
`define PREDECODE_VECTOR__

`include "vector_instruction.sv"

function automatic Frontend::Predecoded predecode_vector(const ref Vector_instruction vinst);
  import Frontend::*;

  Frontend::Predecoded rv;

  // default assignment
  rv = predecoded_zeros();

  if( vinst.opcd != Pu_inst::Op_nve_xo ) 
    return rv;

  rv.ra = vinst.ra;
  rv.rb = vinst.rb;
  rv.rt = vinst.rt;
  rv.fu_set = Frontend::FUB_VECTOR;
  rv.nd_latency = 1'b1;

  return rv;
endfunction

`endif

