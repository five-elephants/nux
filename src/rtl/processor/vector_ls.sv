// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_ls
  #(parameter int THIS_SLICE = 0,
    parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int VRF_SIZE = 32,
    parameter int SCALAR_SIZE = 32 )
  ( input logic clk, reset,
    Vector_ls_ctrl_if.vls ctrl,
    input logic[NUM_ELEMS*ELEM_SIZE-1:0] a,
    output logic[NUM_ELEMS*ELEM_SIZE-1:0] y,
    input logic[SCALAR_SIZE-1:0] load_in,
    input logic[SCALAR_SIZE-1:0] store_serial_in,
    output logic[SCALAR_SIZE-1:0] store_serial_out );

  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------
 
  localparam int NUM_SCALARS = (NUM_ELEMS*ELEM_SIZE)/SCALAR_SIZE;

  typedef logic[NUM_ELEMS*ELEM_SIZE-1:0] Vector;
  typedef logic[SCALAR_SIZE-1:0] Scalar;
  typedef Scalar[0:NUM_SCALARS-1] Vector_as_scalars;


  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------
  
  Vector_as_scalars v;


  //--------------------------------------------------------------------------------
  // Datapath
  //--------------------------------------------------------------------------------
  
  always_ff @(posedge clk) begin
    if( ctrl.load_en[THIS_SLICE] ) begin
      v[ctrl.sel_word] <= load_in;
    end else if( ctrl.store_en ) begin
      v <= a;
    end
  end


  assign y = v;


  //--------------------------------------------------------------------------------
  // Output serialization for store
  //--------------------------------------------------------------------------------
  
  always_comb begin
    if( ctrl.serial_output[THIS_SLICE] )
      store_serial_out = v[ctrl.sel_store_word];
    else
      store_serial_out = store_serial_in;
  end

endmodule
    

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
