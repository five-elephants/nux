// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef VECTOR_STATE__
`define VECTOR_STATE__

class Vector_state 
  #(int NUM_SLICES = 8,
    int NUM_ELEMS = 8,
    int ELEM_SIZE = 16,
    int VRF_SIZE = 32);

  localparam int WORDS_PER_VECTOR = (NUM_ELEMS*ELEM_SIZE)/$bits(Pu_types::Word);
  localparam int HALFWORDS_PER_VECTOR = (NUM_ELEMS*ELEM_SIZE)/($bits(Pu_types::Word)/2);
  localparam int BYTES_PER_VECTOR = (NUM_ELEMS*ELEM_SIZE)/($bits(Pu_types::Word)/4);

  typedef logic[2*ELEM_SIZE-1:0] Vector_double_element;
  typedef logic[ELEM_SIZE-1:0] Vector_element;
  typedef logic[ELEM_SIZE/2-1:0] Vector_half_element;
  typedef logic[ELEM_SIZE/4-1:0] Vector_quarter_element;
  typedef Vector_double_element Double_vector[0:NUM_ELEMS-1];
  typedef Vector_element Vector[0:NUM_ELEMS-1];
  typedef Vector_half_element[0:1] Vector_element_halfs;
  typedef Vector_quarter_element[0:3] Vector_element_quarters;
  typedef logic[NUM_ELEMS*ELEM_SIZE-1:0] Vector_bits;
  typedef Pu_types::Word Vector_words[0:WORDS_PER_VECTOR-1];
  typedef Vector_element Vector_double_bytes[0:BYTES_PER_VECTOR-1];
  typedef Vector_half_element Vector_bytes[0:BYTES_PER_VECTOR-1];
  typedef Compare Vector_condition_register[0:NUM_ELEMS-1];
  typedef logic[NUM_SLICES][NUM_ELEMS*ELEM_SIZE-1:0] Vector_array;

  rand Vector vrf[NUM_SLICES][VRF_SIZE];
  Double_vector accumulator[NUM_SLICES];
  Vector_condition_register vcr[NUM_SLICES];
  Vector_array pmem[Pu_types::Address] = '{default: '0};


  constraint math_corner_values {
    foreach(vrf[i,j,k]) {
      vrf[i][j][k] dist {
        {ELEM_SIZE{1'b1}} := 1,
        {ELEM_SIZE{1'b0}} := 1,
        {1'b1, {ELEM_SIZE-1{1'b0}}} := 1,
        {1'b0, {ELEM_SIZE-1{1'b1}}} := 1,
        [ 0 : {ELEM_SIZE{1'b1}} ] :/ 10
      };
    }
  }


  function new();
    for(int slice_i=0; slice_i<NUM_SLICES; slice_i++) begin
      for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
        accumulator[slice_i][elem_i] = '0;
        vcr[slice_i][elem_i] = '0;
      end

    end 
  endfunction


  function void print();
    for(int reg_i=0; reg_i<VRF_SIZE; reg_i++) begin
      print_vector(reg_i);
    end
  endfunction


  function void print_vector(int i);
    $write("%2d:", i);
    for(int slice_i=0; slice_i<NUM_SLICES; slice_i++) begin
      $write("  ");
      for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
        $write(" %h", vrf[slice_i][i][elem_i]);
      end

      if( ((slice_i+1) % 4 == 0) && (slice_i > 0) ) begin
        $write("\n   ");
      end
    end

    $write("\n");
  endfunction


  function bit is_equal_to(const ref Vector_state #(NUM_SLICES, NUM_ELEMS, ELEM_SIZE, VRF_SIZE) other);
    bit rv;
    const int max_out = 8;
    int out;
    Pu_types::Address iter;
    Pu_types::Word mem_word;

    rv = 1'b1;
    out = 0;

    for(int slice_i=0; slice_i<NUM_SLICES; slice_i++)
      for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++)
        if( accumulator[slice_i][elem_i] !== other.accumulator[slice_i][elem_i] ) begin
          rv = 1'b0;
          if( out++ < max_out )
            $display("mismatch at ACCUMULATOR[slice=%2d][elem=%d]: %h != %h",
              slice_i, elem_i, accumulator[slice_i][elem_i], other.accumulator[slice_i][elem_i]);
        end

    if( out > max_out ) begin
      $display("... (more mismatches not shown) ...");
    end

    out = 0;
    for(int slice_i=0; slice_i<NUM_SLICES; slice_i++)
      for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++)
        if( vcr[slice_i][elem_i] !== other.vcr[slice_i][elem_i] ) begin
          rv = 1'b0;
          if( out++ < max_out )
            $display("mismatch at VCR[slice=%2d][elem=%d]: %h != %h",
              slice_i, elem_i, vcr[slice_i][elem_i], other.vcr[slice_i][elem_i]);
        end

    if( out > max_out ) begin
      $display("... (more mismatches not shown) ...");
    end

    out = 0;
    for(int reg_i=0; reg_i<VRF_SIZE; reg_i++) 
      for(int slice_i=0; slice_i<NUM_SLICES; slice_i++) 
        for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) 
          if( vrf[slice_i][reg_i][elem_i] !== other.vrf[slice_i][reg_i][elem_i] ) begin
            rv = 1'b0;
            if( out++ < max_out )
              $display("mismatch at VRF[slice=%2d][reg=%2d][elem=%2d]: %h != %h",
                slice_i, reg_i, elem_i, vrf[slice_i][reg_i][elem_i], other.vrf[slice_i][reg_i][elem_i]);
          end

    if( out > max_out ) begin
      $display("... (more mismatches not shown) ...");
    end


    // compare parallel memory
    out = 0;
    if( pmem.first(iter) ) begin
      do
        for(int slice_i=0; slice_i<NUM_SLICES; slice_i++) 
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++)
            if( other.pmem[iter] !== pmem[iter] ) begin
              rv = 1'b0;
              if( out++ < max_out )
                $display("mismatch at PMEM[address=0x%8h][slice=%2d][elem=%2d]: %h != %h",
                  iter, slice_i, elem_i, other.pmem[iter], pmem[iter]);
            end
      while( pmem.next(iter) );
    end

    if( other.pmem.first(iter) ) begin
      do
        for(int slice_i=0; slice_i<NUM_SLICES; slice_i++) 
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++)
            if( other.pmem[iter] !== pmem[iter] ) begin
              rv = 1'b0;
              if( out++ < max_out )
                $display("mismatch at PMEM[address=0x%8h][slice=%2d][elem=%2d]: %h != %h",
                  iter, slice_i, elem_i, other.pmem[iter], pmem[iter]);
            end
      while( other.pmem.next(iter) );
    end

    return rv;
  endfunction

endclass

`endif


/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
