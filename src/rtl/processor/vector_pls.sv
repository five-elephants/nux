// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_pls
  #(parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int ENABLES_PER_ELEMENT = 4 )
  ( input logic clk, reset,
    Vector_pls_ctrl_if.pls ctrl,
    input logic[NUM_ELEMS*ELEM_SIZE-1:0] a,
    input Vector::Compare[0:NUM_ELEMS-1] vcr,
    output logic[NUM_ELEMS*ELEM_SIZE-1:0] y,
    output logic[0:ENABLES_PER_ELEMENT-1] write_mask[0:NUM_ELEMS-1],
    
    input logic[NUM_ELEMS*ELEM_SIZE-1:0] sdata,
    output logic[NUM_ELEMS*ELEM_SIZE-1:0] mdata,
    output logic[(NUM_ELEMS*ELEM_SIZE / 8)-1:0] mbyteen);


  localparam int ELEM_BYTE_SIZE = ELEM_SIZE / 8;
  localparam int ENABLES_PER_BYTE = ENABLES_PER_ELEMENT / ELEM_BYTE_SIZE;

  typedef logic[(NUM_ELEMS*ELEM_SIZE / 8)-1:0] Byte_en;


  Byte_en mbyteen_i, next_mbyteen;
  Vector::Compare[0:NUM_ELEMS-1] vcr_d;


  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      vcr_d <= '0;
    end else begin
      if( ctrl.capture )
        vcr_d <= vcr;
    end


  always_comb begin
    mdata = a;
    y = sdata;

    for(int i=0; i<NUM_ELEMS; i++) begin
      unique case(ctrl.cond)
        Pu_inst::Fxv_cond_eq:
          next_mbyteen[$bits(next_mbyteen) - i*ELEM_BYTE_SIZE -1 -: ELEM_BYTE_SIZE] = {
            vcr_d[i].eq[0] | vcr_d[i].eq[1],
            vcr_d[i].eq[2] | vcr_d[i].eq[3]
          };
        Pu_inst::Fxv_cond_lt:
          next_mbyteen[$bits(next_mbyteen) - i*ELEM_BYTE_SIZE -1 -: ELEM_BYTE_SIZE] = {
            vcr_d[i].lt[0] | vcr_d[i].lt[1],
            vcr_d[i].lt[2] | vcr_d[i].lt[3]
          };
        Pu_inst::Fxv_cond_gt:
          next_mbyteen[$bits(next_mbyteen) - i*ELEM_BYTE_SIZE -1 -: ELEM_BYTE_SIZE] = {
            vcr_d[i].gt[0] | vcr_d[i].gt[1],
            vcr_d[i].gt[2] | vcr_d[i].gt[3]
          };

        default:
          next_mbyteen[$bits(next_mbyteen) - i*ELEM_BYTE_SIZE -1 -: ELEM_BYTE_SIZE] = 2'b11;
      endcase
    end
  end


  assign mbyteen_i = next_mbyteen;
  assign mbyteen = mbyteen_i;

  always_comb begin
    for(int i=0; i<NUM_ELEMS; i++) begin
      write_mask[i] = '1;
    end
  end

endmodule
    
