// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Branch
  ( input logic clk,
    input logic reset,

    Branch_ctrl_if.branch       ctrl,
    Branch_data_if.branch       data,
    

    Write_back_data_if.branch   write_back,
    Inst_fetch_ctrl_if.branch   inst_fetch );

import Pu_types::*;

logic ctr_ok;
logic cond_ok;
logic[31:0] ctr;


always_comb
begin : decrement_counter
  if( ctrl.dec_ctr )
    ctr <= data.ctr - 1;
  else 
    ctr <= data.ctr;
end : decrement_counter


assign cond_ok = ctrl.mask_cond 
    || (data.cr[31-ctrl.crbi] == ctrl.cond);
assign ctr_ok = ctrl.mask_ctr 
    | ((ctr != 0) ^ ctrl.ctr_eq);


always_ff @(posedge clk or posedge reset)
begin : set_jump
  if( reset ) begin
    inst_fetch.jump <= 1'b0;
    //write_back.ctr_we <= 1'b0;
    //write_back.lnk_we <= 1'b0;
  end else begin
    // default assignment
    inst_fetch.jump <= 1'b0;
    //write_back.ctr_we <= 1'b0;
    //write_back.lnk_we <= 1'b0;

    if( ctrl.en ) begin
      //write_back.ctr_we <= ctrl.dec_ctr;
      //write_back.lnk_we <= ctrl.save_link;

      if( ctrl.jump ) begin
        inst_fetch.jump <= 1'b1;
      end else begin
        if( ctr_ok && cond_ok ) begin
          inst_fetch.jump <= 1'b1;
        end
      end
    end
  end
end : set_jump

always_ff @(posedge clk)
begin : reg_ctr
  write_back.ctr <= ctr;
end : reg_ctr


endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
