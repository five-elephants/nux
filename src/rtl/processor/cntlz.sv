// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Cntlz
  ( input Pu_types::Word x,
    output Pu_types::Word y,
    output Pu_types::Cr_field crout );

import Pu_types::*;

localparam a_width = DWIDTH;
localparam addr_width = $clog2(a_width) +1;

logic[addr_width-1:0] cnt;

//`include "DW_lzd_function.inc"

DW_lzd #(a_width) lzd ( .a(x), .dec(), .enc(cnt) );

//assign cnt = DWF_lzd_enc(x);
assign y = (cnt[addr_width-1] == 1'b1) ? 32'h20 : { {DWIDTH-addr_width{1'b0}}, cnt };


always_comb begin
  // default assignment
  crout = '0;

  if( cnt == 0 )
    crout.eq = 1'b1;
  else
    crout.gt = 1'b1;
end


endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
