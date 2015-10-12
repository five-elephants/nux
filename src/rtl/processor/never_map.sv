// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Never_map
  #(parameter int WIDTH = 32)
  ( input Pu_types::Nve_lut lut,
    input logic[WIDTH-1:0] a,
    output logic[WIDTH-1:0] res );

  import Pu_types::*;

  localparam int NUM_NIBBLES = WIDTH / 4;

  generate
    genvar i;
    for(i=0; i<NUM_NIBBLES; i++) begin : gen_map

      logic[3:0] m_in, m_out;

      assign m_in = a[(i+1)*4-1:i*4];

      always_comb begin
        m_out = lut[m_in];
      end

      assign res[(i+1)*4-1:i*4] = m_out;

    end : gen_map
  endgenerate

endmodule 

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
