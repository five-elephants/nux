// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Vector_ls_ctrl_if
  #(parameter int NUM_SLICES = 1,
    parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int SCALAR_SIZE = 32)
  ();

  localparam int VECTOR_SIZE = NUM_ELEMS * ELEM_SIZE;
  localparam int NUM_SCALARS_PER_VECTOR = VECTOR_SIZE / SCALAR_SIZE;
  localparam int NUM_SCALARS = NUM_SCALARS_PER_VECTOR * NUM_SLICES;

  logic load_en[0:NUM_ELEMS-1];
  logic[$clog2(NUM_SCALARS_PER_VECTOR)-1:0] sel_word;
  logic[$clog2(NUM_SCALARS_PER_VECTOR)-1:0] sel_store_word;
  logic store_en;
  logic serial_output[0:NUM_SLICES-1];

  logic new_op;
  logic[$clog2(NUM_SCALARS):0] count;
  logic we;
  logic complete;

  Pu_types::Word g;

  modport ctrl(
    output new_op, count, we, store_en, g,
    input complete
  );  

  modport vls(
    input load_en, sel_word, store_en, serial_output, sel_store_word
  );

  modport shared (
    output load_en, sel_word, serial_output, sel_store_word,
    input new_op, count, we, g,
    output complete
  );

endinterface

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
