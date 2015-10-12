// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Delayed_wb_if #(parameter int DEST_SIZE = 5) ();
  logic delayed;
  logic wb_req;
  logic[DEST_SIZE-1:0] wb_dest;
  logic wb_dest_valid;
  logic wb_ack;
  logic wb_cancel;
  
  logic scheduled_wb;
  logic[DEST_SIZE-1:0] track_dest;
  logic track_valid;

  modport fub(
    output delayed, wb_req, wb_dest, wb_dest_valid, wb_cancel, scheduled_wb,
      track_dest, track_valid,
    input wb_ack
  );

  modport frontend(
    input delayed, wb_req, wb_dest, wb_dest_valid, wb_cancel, scheduled_wb,
      track_dest, track_valid,
    output wb_ack
  );

  modport inst_track(
    input delayed, wb_dest, wb_dest_valid, track_dest, track_valid,
      wb_ack, wb_req
  );
endinterface


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
