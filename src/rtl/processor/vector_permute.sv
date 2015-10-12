// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_permute
  #(parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16)
  ( input logic clk, reset,
    Vector_permute_ctrl_if.permute ctrl,
    input Vector::Compare[0:NUM_ELEMS-1] vcr,
    input logic[NUM_ELEMS*ELEM_SIZE-1:0] a,
    input logic[NUM_ELEMS*ELEM_SIZE-1:0] b,
    output logic[NUM_ELEMS*ELEM_SIZE-1:0] y );

  localparam int HALF_SIZE = ELEM_SIZE/2;
  localparam int NUM_HALF_ELEMS = NUM_ELEMS*2;

  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------

  typedef logic[NUM_ELEMS*ELEM_SIZE-1:0] Vec;
  typedef logic[0:2*NUM_HALF_ELEMS-1][HALF_SIZE-1:0] Double_vector;
  typedef logic[0:NUM_HALF_ELEMS-1][HALF_SIZE-1:0] Single_vector;


  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------

  Double_vector src;
  Single_vector src_a, src_b;
  Single_vector tgt;
  Vec next_y;


  //--------------------------------------------------------------------------------
  // Functions
  //--------------------------------------------------------------------------------

  function automatic Vec splat(logic[ELEM_SIZE-1:0] v);
    Vec rv;

    for(int i=ELEM_SIZE*NUM_ELEMS-1; i>0; i -= ELEM_SIZE)
      rv[i -: ELEM_SIZE] = v;

    return rv;
  endfunction


  function automatic Vec splatb(logic[ELEM_SIZE/2-1:0] v);
    Vec rv;

    for(int i=ELEM_SIZE*NUM_ELEMS-1; i>0; i -= ELEM_SIZE/2)
      rv[i -: ELEM_SIZE/2] = v;

    return rv;
  endfunction


  function automatic Vec shifth(Vec v, logic signed[4:0] sh);
    Vec rv;

    for(int i=0; i<NUM_ELEMS; i++) begin
      for(int j=0; j<ELEM_SIZE; j++) begin
        if( (j - sh >= 0) && (j - sh < ELEM_SIZE) )
          rv[(i*ELEM_SIZE) + j] = v[(i*ELEM_SIZE) + j - sh];
        else
          rv[(i*ELEM_SIZE) + j] = 1'b0;
      end
    end

    return rv;
  endfunction


  function automatic Vec shiftb(Vec v, logic signed[4:0] sh);
    Vec rv;

    for(int i=0; i<2*NUM_ELEMS; i++) begin
      for(int j=0; j<ELEM_SIZE/2; j++) begin
        if( (j - sh >= 0) && (j - sh < ELEM_SIZE/2) )
          rv[(i*ELEM_SIZE/2) + j] = v[(i*ELEM_SIZE/2) + j - sh];
        else
          rv[(i*ELEM_SIZE/2) + j] = 1'b0;
      end
    end

    return rv;
  endfunction


  function automatic Vec select(Vec a, Vec b, Pu_inst::Fxv_cond cond, Vector::Compare[0:NUM_ELEMS-1] vcr);
    Vec rv;

    for(int i=0; i<NUM_ELEMS; i++) begin
      for(int k=0; k<2; k++) begin
        for(int j=0; j<ELEM_SIZE/2; j++) begin
          int ai;

          ai = (NUM_ELEMS * ELEM_SIZE) - ((i*ELEM_SIZE) + (k*ELEM_SIZE/2) + j) - 1;

          unique case(cond)
            Pu_inst::Fxv_cond_eq: begin
              if( vcr[i].eq[2*k] )
                rv[ai] = b[ai];
              else
                rv[ai] = a[ai];
            end

            Pu_inst::Fxv_cond_gt: begin
              if( vcr[i].gt[2*k] )
                rv[ai] = b[ai];
              else
                rv[ai] = a[ai];
            end

            Pu_inst::Fxv_cond_lt: begin
              if( vcr[i].lt[2*k] )
                rv[ai] = b[ai];
              else
                rv[ai] = a[ai];
            end

            Pu_inst::Fxv_cond_null: begin
              rv[ai] = b[ai];
            end
          endcase
        end
      end
    end

    return rv;
  endfunction

  //--------------------------------------------------------------------------------
  // Datapath
  //--------------------------------------------------------------------------------

  assign src = {a, b};
  assign src_a = a;
  assign src_b = b;


  always_comb begin
    unique case({ctrl.pack_upper, ctrl.pack_lower, ctrl.unpack_left, ctrl.unpack_right})
      4'b1000: begin
        for(int i=0; i<NUM_HALF_ELEMS; i++) begin
          tgt[i] = '0;

          /*for(int j=0; j<(8-ctrl.size); j++) begin
            tgt[i][8-ctrl.size -1 - j] = src[2*i][$left(src[2*i]) - j];
          end*/

          for(int j=0; j<8; j++) begin
            if( j+ctrl.size < 8 )
              tgt[i][8-ctrl.size -1 - j] = src[2*i][HALF_SIZE-1 - j];
          end
        end
      end

      4'b0100: begin
        for(int i=0; i<NUM_HALF_ELEMS; i++) begin
          tgt[i] = '0;
          for(int j=0; j<ctrl.size; j++) begin
            tgt[i][8-ctrl.size -1 -j] = src[2*i][HALF_SIZE-1 - (8 - ctrl.size) - j];
          end

          //for(int j=0; j<(8 - ctrl.size) - ctrl.size; j++) begin
          for(int j=0; j<8; j++) begin
            if( j + 2*ctrl.size < 8 )
              tgt[i][8-2*ctrl.size - 1 - j] = src[2*i+1][HALF_SIZE-1 - j];
          end
        end
      end

      4'b0010: begin
        for(int i=0; i<NUM_HALF_ELEMS/2; i++) begin
          tgt[2*i] = '0;
          tgt[2*i+1] = '0;

          for(int j=0; j<8; j++)
            if( j+ctrl.size < 8 )
              tgt[2*i][7 - j] = src_a[i][7 - ctrl.size - j];

          for(int j=0; j<ctrl.size; j++)
            tgt[2*i][ctrl.size - 1 - j] = src_b[i][7 - ctrl.size - j];

          for(int j=0; j<8; j++)
            if( j + 2*ctrl.size < 8 )
              tgt[2*i+1][7 - j] = src_b[i][7 - 2*ctrl.size - j];
        end
      end

      4'b0001: begin
        for(int i=0; i<NUM_HALF_ELEMS/2; i++) begin
          tgt[2*i] = '0;
          tgt[2*i+1] = '0;

          //for(int j=0; j<8 - sz; j++)
          for(int j=0; j<8; j++)
            if( j + ctrl.size < 8 )
              tgt[2*i][7 - j] = src_a[i + NUM_HALF_ELEMS/2][7 - ctrl.size - j];

          for(int j=0; j<ctrl.size; j++)
            tgt[2*i][ctrl.size - 1 - j] = src_b[i + NUM_HALF_ELEMS/2][7 - ctrl.size - j];

          //for(int j=0; j<8 - 2*ctrl.size; j++)
          for(int j=0; j<8; j++)
            if( j + 2*ctrl.size < 8 )
              tgt[2*i+1][7 - j] = src_b[i + NUM_HALF_ELEMS/2][7 - 2*ctrl.size - j];
        end
      end

      default: begin
        tgt = 'x;
      end
    endcase
  end


  always_comb begin : result_mux
    unique case(ctrl.op)
      Vector::PERMUTE_PACK:   next_y = tgt;
      Vector::PERMUTE_SPLAT:  next_y = splat(ctrl.g);
      Vector::PERMUTE_SPLATB: next_y = splatb(ctrl.g);
      Vector::PERMUTE_SHIFT:  next_y = shifth(a, ctrl.shift);
      Vector::PERMUTE_SHIFTB: next_y = shiftb(a, ctrl.shift);
      Vector::PERMUTE_SELECT: next_y = select(a, b, ctrl.size, vcr);
      default:                next_y = 'x;
    endcase
  end

  always_ff @(posedge clk) begin
    if( ctrl.keep_res )
      y <= next_y;
  end

endmodule


/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
