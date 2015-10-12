// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module Lookup_cache
  #(parameter int SIZE = 32,
    parameter bit WRITE_THROUGH = 1'b0,
    parameter int NUM_CLEAR_PORTS = 1)
  ( input logic clk, reset,
    input logic[Pu_types::clog2(SIZE)-1:0]  set_addr,
    input logic                             set,
    input logic[Pu_types::clog2(SIZE)-1:0]  clear_addr[0:NUM_CLEAR_PORTS-1],
    input logic                             clear[0:NUM_CLEAR_PORTS-1],
    input logic[Pu_types::clog2(SIZE)-1:0]  test_addr,
    output logic                            found,
    output logic                            empty );

typedef logic[Pu_types::clog2(SIZE)-1:0] Address;

logic v_set[0:SIZE-1];
logic v_clear[0:NUM_CLEAR_PORTS-1][0:SIZE-1];
logic cell_clear[0:SIZE-1];
logic q[0:SIZE-1];

generate
  genvar i;
  for(i=0; i<SIZE; i++) begin : gen_cells

    always_comb begin
      cell_clear[i] = 1'b0;
      for(int p=0; p<NUM_CLEAR_PORTS; p++)
        cell_clear[i] = cell_clear[i] | v_clear[p][i];
    end

    always_ff @(posedge clk or posedge reset)
      if( reset )
        q[i] <= 1'b0;
      else
        unique case({v_set[i], cell_clear[i]})
          2'b10:    q[i] <= 1'b1;
          2'b01:    q[i] <= 1'b0;
          2'b00:    q[i] <= q[i];
          2'b11:    q[i] <= 1'b1;
          default:  q[i] <= 1'bx;
        endcase

  end : gen_cells
endgenerate

always_comb begin
  for(int unsigned i=0; i<SIZE; i++) begin
    if( i == set_addr )
      v_set[i] = set;
    else
      v_set[i] = 1'b0;

    for(int unsigned p=0; p<NUM_CLEAR_PORTS; p++) 
      if( i == clear_addr[p] )
        v_clear[p][i] = clear[p];
      else
        v_clear[p][i] = 1'b0;
  end
end

/** Test if cache is empty, */
always_comb begin
  empty = 1'b1;

  for(int unsigned i=0; i<SIZE; i++)
    if( q[i] )
      empty = 1'b0;
end

generate
  if( WRITE_THROUGH ) begin : gen_write_through

    always_comb begin
      found = 1'b0;

      for(int unsigned i=0; i<SIZE; i++)
        if( i == test_addr )
          found = q[i] & ~cell_clear[i];
    end
    //assign found = q[test_addr] & ~cell_clear[test_addr];

  end else begin : gen_no_write_through

    always_comb begin
      found = 1'b0;

      for(int unsigned i=0; i<SIZE; i++)
        if( i == test_addr )
          found = q[i];
    end
    //assign found = q[test_addr];

  end
endgenerate

endmodule




// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
