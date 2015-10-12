/** _use_m4_ macros
 * include(ops.m4)
 */

// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Fub_never
  #(parameter int NUM_LUTS = 2)
  ( input logic clk, reset,
    
    input Frontend::Issue_slot inst,
    Operand_if.read opbus,

    output Backend::Result_bus resbus );

  import Backend::*;
  import Pu_inst::*;
  import Pu_types::*;

  //---------------------------------------------------------------------------
  // Local types and signals
  //---------------------------------------------------------------------------
  
  typedef logic[3:0] Nibble;
  typedef Nibble[0:15] Lookup_table;
  typedef logic[clog2(NUM_LUTS)-1:0] Lut_index;
  typedef logic[7:0] Select_state;

  Lookup_table lut[0:NUM_LUTS-1];
  Inst ir;
  Word aa, bb, cc;
  Word map_res;
  Word select_res;
  Lut_index next_lut_sel, lut_sel;
  Select_state next_select_state, select_state;
  logic next_save_select_state, save_select_state;
  logic next_output_map, output_map;
  logic next_save_lut, save_lut;

  //---------------------------------------------------------------------------
  // Decode
  //---------------------------------------------------------------------------
  
  assign ir = inst.ir;
  assign aa = opbus.opbus_0.a;
  assign bb = opbus.opbus_0.b;
  assign cc = opbus.opbus_0.c;
 
  always_comb begin
    // default assignment
    next_output_map = 1'b0;
    next_save_select_state = 1'b0;
    next_save_lut = 1'b0;
    next_lut_sel = '0;

    OPCMP(ir)
      OPX2(Op_nve_xo, Xop_nvem): begin
        next_output_map = 1'b1;
        next_lut_sel = ir.x.rb;
      end

      OP(Op_nvecmpi):
        next_save_select_state = 1'b1;

      OPX2(Op_nve_xo, Xop_nvemtl): begin
        next_save_lut = 1'b1;
        next_lut_sel = ir.x.rt;
      end

      default: begin end
    ENDOPCMP
  end 
  
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      lut_sel <= '0;
      output_map <= 1'b0;
      save_lut <= 1'b0;
      save_select_state <= 1'b0;
    end else begin
      //if( inst.valid ) begin
        output_map <= next_output_map;
        save_lut <= next_save_lut;
        lut_sel <= next_lut_sel;
        save_select_state <= next_save_select_state;
      //end
    end

  //---------------------------------------------------------------------------
  // Datapath
  //---------------------------------------------------------------------------
 
  /** Lookup table register */
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      for(int i=0; i<NUM_NVE_LUT; i++)
        lut[i] <= '0;
    end else begin
      if( save_lut ) begin
        lut[lut_sel] <= {aa, bb};
      end
    end
  
  Never_map map (
    .lut(lut[lut_sel]),
    .a(aa),
    .res(map_res)
  );

  Never_select select (
    .sel(select_state),
    .a(aa),
    .b(bb),
    .res(select_res)
  );

  Never_compare compare (
    .a(aa),
    .pattern(bb[3:0]),
    .mask('1),
    .out_mask(next_select_state),
    .zero()
  );

  /** Internal selection state */
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      select_state <= '0;
    end else begin
      if( save_select_state )
        select_state <= next_select_state;
    end

  /** Output */
  always_comb begin
    resbus.valid = 1'b1;
    resbus.crf = '0;
    resbus.ov = 1'b0;
    resbus.cout = 1'b0;
    resbus.res_b = '0;
    resbus.msr = '0;
    
    if( output_map )
      resbus.res_a = map_res;
    else
      resbus.res_a = select_res;
  end

  /*always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      resbus.res_a <= '0;
      resbus.crf <= '0;
      resbus.ov <= 1'b0;
      resbus.cout <= 1'b0;
      resbus.res_b <= '0;
      resbus.msr <= '0;
    end else begin
      resbus.crf <= '0;
      resbus.ov <= 1'b0;
      resbus.cout <= 1'b0;
      resbus.res_b <= '0;
      resbus.msr <= '0;
      
      if( output_map )
        resbus.res_a <= map_res;
      else
        resbus.res_a <= select_res;
    end*/
  
endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
