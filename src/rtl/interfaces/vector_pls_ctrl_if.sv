// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Vector_pls_ctrl_if
  #(parameter int BUS_ADDR_WIDTH = 32,
    parameter int BUS_DATA_WIDTH = 128)
  ();

  logic capture;
  logic stored_byteen;
  Pu_inst::Fxv_cond cond;

  // for external bus control
  Bus::Ocp_cmd MCmd;
  logic MRespAccept;
  logic[BUS_ADDR_WIDTH-1:0] MAddr;
  logic[BUS_DATA_WIDTH/8-1:0] MByteEn;
  
  Bus::Ocp_resp SResp;
  logic SCmdAccept;


  modport ctrl (
    output capture, stored_byteen, cond,
    output MCmd, MAddr, MRespAccept, MByteEn,
    input SResp, SCmdAccept
  );

  modport pls (
    input capture, stored_byteen, cond
  );

  modport shared (
    input MCmd, MAddr, MRespAccept, MByteEn,
    output SResp, SCmdAccept
  );

endinterface
