// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vrf_wb_arb
  #(parameter int NUM_UNITS=1)
  ( input logic clk, reset,
    input logic reqs[0:NUM_UNITS-1],
    output logic acks[0:NUM_UNITS-1],
    input logic ens[0:NUM_UNITS-1],
    input logic wes[0:NUM_UNITS-1],
    input Vector::Vrf_index addrs[0:NUM_UNITS-1],
    input Vector::Rs_ref refs[0:NUM_UNITS-1],
    output logic vrf_wb_en,
    output logic vrf_wb_we,
    output Vector::Vrf_index vrf_wb_addr,
    output Vector::Rs_ref vrf_wb_ref,
    output Vector::Unit vrf_src_unit );


  //import Vector::*;

  // arbitrate wb requests
  always_comb begin
    Vector::Unit_id winner;

    // default assignments
    vrf_wb_en = 1'b0;
    vrf_wb_we = 1'b0;
    vrf_wb_addr = '0;
    for(int i=0; i<$bits(acks); i++)
      acks[i] = 1'b0;
    winner = Vector::VU_ID_MADD;

    // arbitration
    if( reqs[Vector::VU_ID_MADD] ) 
      winner = Vector::VU_ID_MADD;
    else if( reqs[Vector::VU_ID_CMP] )
      winner = Vector::VU_ID_CMP;
    else if( reqs[Vector::VU_ID_LS] )
      winner = Vector::VU_ID_LS;

    vrf_wb_en = ens[winner];
    vrf_wb_we = wes[winner];
    vrf_wb_addr = addrs[winner];
    vrf_wb_ref = refs[winner];
    acks[winner] = reqs[winner];
    vrf_src_unit = Vector::unit_id_to_unit(winner);
  end

endmodule

