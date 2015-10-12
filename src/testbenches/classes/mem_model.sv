// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef MEM_MODEL__
`define MEM_MODEL__

virtual class Mem_model;
	pure virtual function Pu_types::Word get(input Pu_types::Address address);
	pure virtual function void set(input Pu_types::Address address, Pu_types::Word data);
	pure virtual function bit iter_first(ref Pu_types::Address iter, output Pu_types::Word data);
	pure virtual function bit iter_next(ref Pu_types::Address iter, output Pu_types::Word data);
	pure virtual function void clear(input Pu_types::Address from);

	pure virtual function void update_from(const ref Mem_model other);

	pure virtual function int get_mem_size();
endclass


function automatic bit compare_mem(input Mem_model a, b);
  bit rv = 1;
  Pu_types::Address iter;
  Word w;

  if( a.iter_first(iter, w) ) begin
    do
      if( w !=? b.get(iter) ) begin
        $display("mismatch at address %h: a: %h !=? b: %h",
            iter, w, b.get(iter));
        rv = 0;
        return rv;
      end 
    while( a.iter_next(iter, w) );
  end

  if( b.iter_first(iter, w) ) begin
    do
      if( w !=? a.get(iter) ) begin
        $display("mismatch at address %h: b: %h !=? a: %h",
            iter, w, a.get(iter));
        rv = 0;
        return rv;
      end 
    while( b.iter_next(iter, w) );
  end

  return rv;
endfunction

`endif

