// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Syn_io_if();

  logic busy;
  logic start;
  Syn_io::Op op;

  logic client2syn_valid;
  Syn_io::Data client2syn_data;
  Syn_io::Eval_pattern[0:3] client2syn_patterns;

  logic syn2client_valid;
  Syn_io::Data syn2client_data;
  logic syn2client_channel;
  logic[1:0] syn2client_pat_ctr;

  modport client (
    input busy, syn2client_channel, syn2client_valid, syn2client_data, syn2client_pat_ctr,
    output start, op, client2syn_valid, client2syn_data, client2syn_patterns
  );

  modport syn (
    output busy, syn2client_channel, syn2client_valid, syn2client_data, syn2client_pat_ctr,
    input start, op, client2syn_valid, client2syn_data, client2syn_patterns
  );

endinterface

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
