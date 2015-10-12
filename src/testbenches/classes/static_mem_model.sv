// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef STATIC_MEM_MODEL__
`define STATIC_MEM_MODEL__

`include "mem_model.sv"

class Static_mem_model extends Mem_model;
  Pu_types::Word default_return;

  //---------------------------------------------------------------------------
  function new(input Pu_types::Word default_return = 0);
    this.default_return = default_return; 
  endfunction
  //---------------------------------------------------------------------------
	virtual function Pu_types::Word get(input Pu_types::Address address);
    return default_return;
  endfunction
  //---------------------------------------------------------------------------
	virtual function void set(input Pu_types::Address address, Pu_types::Word data);
  endfunction
  //---------------------------------------------------------------------------
	virtual function bit iter_first(ref Pu_types::Address iter, output Pu_types::Word data);
    data = 0;
    return 1'b0;
  endfunction
  //---------------------------------------------------------------------------
	virtual function bit iter_next(ref Pu_types::Address iter, output Pu_types::Word data);
    data = 0;
    return 1'b0;
  endfunction
  //---------------------------------------------------------------------------
	virtual function void clear(input Pu_types::Address from);
  endfunction
  //---------------------------------------------------------------------------
	virtual function void update_from(const ref Mem_model other);
  endfunction
  //---------------------------------------------------------------------------
	virtual function int get_mem_size();
    return 0;
  endfunction
  //---------------------------------------------------------------------------
endclass

`endif


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
