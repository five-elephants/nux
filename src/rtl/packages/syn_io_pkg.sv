// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


package Syn_io;

  typedef enum logic[3:0] {
    OP_IDLE         = 4'h0,
    OP_OPEN_WEIGHTS = 4'h1,
    OP_OPEN_DEC     = 4'h2,
    OP_READ         = 4'h3,
    OP_WRITE        = 4'h4,
    OP_CLOSE        = 4'h5,
    OP_CORR_LOAD    = 4'h6,
    OP_CORR_EVAL    = 4'h7,
    OP_CORR_SAMPLE  = 4'h8,
    OP_CORR_RESET   = 4'h9,

    OP_USER_0       = 4'ha,
    OP_USER_1       = 4'hb,

    //OP_CORR_LOOP    = 4'ha,
    OP_UNDEF        = 4'bxxxx
  } Opcd;

  typedef logic[7:0] Row_addr;
  typedef logic[2:0] Colset_addr;
  typedef logic[127:0] Data;

  typedef struct packed {
    logic evaab;
    logic evacb;
    logic evcab;
    logic evccb;
  } Eval_pattern;

  typedef struct packed {
    Opcd opcd;
    Row_addr row;
    Colset_addr colset;
  } Op;

endpackage

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
