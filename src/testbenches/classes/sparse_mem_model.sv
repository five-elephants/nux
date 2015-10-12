// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef SPARSE_MEM_MODEL__
`define SPARSE_MEM_MODEL__

`include "mem_model.sv"

class Sparse_mem_model extends Mem_model;
	//Word mem[int];
	Word mem[Address];
	const int mem_size;
	const bit default_random;

	//---------------------------------------------------------------------------
	function new(input int sz = 1024, bit default_random = 1'b0);
		mem_size = sz;
		this.default_random = default_random;
	endfunction
	//---------------------------------------------------------------------------
	virtual function Word get(input Address address);
		Address mem_addr;

		mem_addr = address % mem_size;

		if( mem.exists(mem_addr) ) begin
			return mem[mem_addr];
		end else begin
			if( default_random ) begin
				mem[mem_addr] = $urandom;
				return mem[mem_addr];
			end else begin
				return '0;
			end
		end
	endfunction
	//---------------------------------------------------------------------------
	virtual function void set(input Address address, Word data);
		Address mem_addr;

		mem_addr = address % mem_size;

		mem[mem_addr] = data;
	endfunction
	//---------------------------------------------------------------------------
	virtual function bit iter_first(ref Address iter, output Word data);
		if( mem.first(iter) ) begin
			data = mem[iter];
			return 1'b1;
		end else
			return 1'b0;
	endfunction
	//---------------------------------------------------------------------------
	virtual function bit iter_next(ref Address iter, output Word data);
		if( mem.next(iter) ) begin
			data = mem[iter];
			return 1'b1;
		end else begin
			return 1'b0;
		end
	endfunction
	//---------------------------------------------------------------------------
	virtual function void clear(input Address from);
		Address iter = from;

		if( mem.exists(iter) )
			do 
				mem.delete(iter);
			while( mem.next(iter) );
	endfunction
	//---------------------------------------------------------------------------
	virtual function void update_from(const ref Mem_model other);
		Address iter = 0;
		Word data;

		if( other.iter_first(iter, data) )
			do
				mem[iter] = data;
			while( other.iter_next(iter, data) );
	endfunction
	//---------------------------------------------------------------------------
	virtual function int get_mem_size();
		return mem_size;
	endfunction
	//---------------------------------------------------------------------------
endclass


`endif

