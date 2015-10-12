// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef FIXED_STATE__
`define FIXED_STATE__

`include "sparse_mem_model.sv"

import Pu_types::*;

class Fixed_state extends State;
	Address  pc;
	Word     gpr[0:31];
	Cr_field cr[0:7];
	Word     ctr;
	Word     lnk;
	Word     xer;
	Msr      msr;
	Esr      esr;
	Word     srr0, srr1;
	Word     csrr0, csrr1;
	Word     mcsrr0, mcsrr1;
	Word     dear;
	Word     gout;
	Word     goe;
	Mem_model mem_model;
	Mem_model io_model;
	Nve_sstate nve_sstate;
	Nve_lut  nve_lut[NUM_NVE_LUT];

	//---------------------------------------------------------------------------
	function new(int mem_size = 1024, int io_size = 1024);
		Sparse_mem_model sparse_model;
		Sparse_mem_model sparse_io;

		sparse_model = new(mem_size);
		sparse_io = new(io_size);

		mem_model = sparse_model;
		io_model = sparse_io;
	endfunction
	//---------------------------------------------------------------------------

	extern virtual function Address    get_pc();
	extern virtual function Word       get_gpr(input int index);
	extern virtual function Cr_field   get_cr(input int index);
	extern virtual function Word       get_ctr();
	extern virtual function Word       get_lnk();
	extern virtual function Word       get_xer();
	extern virtual function Word       get_srr0();
	extern virtual function Word       get_srr1();
	extern virtual function Word       get_csrr0();
	extern virtual function Word       get_csrr1();
	extern virtual function Word       get_mcsrr0();
	extern virtual function Word       get_mcsrr1();
	extern virtual function Msr        get_msr();
	extern virtual function Esr        get_esr();
	extern virtual function Word       get_dear();
	extern virtual function Word       get_gout();
	extern virtual function Word       get_goe();
	extern virtual function Word       get_mem(input Address address);
	extern virtual function bit        get_mem_first(ref Address iter, output Word data);
	extern virtual function bit        get_mem_next(ref Address iter, output Word data);

	extern virtual function void       set_pc(input Address p);
	extern virtual function void       set_gpr(input int index, Word w);
	extern virtual function void       set_cr(input int index, Cr_field c);
	extern virtual function void       set_ctr(input Word c);
	extern virtual function void       set_lnk(input Word l);
	extern virtual function void       set_xer(input Word x);
	extern virtual function void       set_srr0(input Word x);
	extern virtual function void       set_srr1(input Word x);
	extern virtual function void       set_csrr0(input Word x);
	extern virtual function void       set_csrr1(input Word x);
	extern virtual function void       set_mcsrr0(input Word x);
	extern virtual function void       set_mcsrr1(input Word x);
	extern virtual function void       set_dear(input Word x);
	extern virtual function void       set_esr(input Esr x);
	extern virtual function void       set_msr(input Msr x);
	extern virtual function void       set_gout(input Word x);
	extern virtual function void       set_goe(input Word x);
	extern virtual function void       set_mem(input int address, Word w);

	extern virtual function void       set_mem_model(ref Mem_model model);
	extern virtual function Mem_model  get_mem_model();

	extern virtual function void       set_io_model(ref Mem_model model);
	extern virtual function Mem_model  get_io_model();

	extern virtual function Nve_sstate get_nve_sstate();
	extern virtual function Nve_lut    get_nve_lut(input int num);
	extern virtual function void       set_nve_sstate(input Nve_sstate sstate);
	extern virtual function void       set_nve_lut(input int num, Nve_lut lut);

	extern virtual function void       copy_from(input State a);
endclass

//---------------------------------------------------------------------------
function Address
Fixed_state::get_pc();
	return pc;
endfunction
//---------------------------------------------------------------------------
function Word
Fixed_state::get_gpr(input int index);
	return gpr[index];
endfunction
//---------------------------------------------------------------------------
function Cr_field
Fixed_state::get_cr(input int index);
	return cr[index];
endfunction
//---------------------------------------------------------------------------
function Word
Fixed_state::get_ctr();
	return ctr;
endfunction
//---------------------------------------------------------------------------
function Word
Fixed_state::get_lnk();
	return lnk;
endfunction
//---------------------------------------------------------------------------
function Word
Fixed_state::get_xer();
	return xer;
endfunction
//---------------------------------------------------------------------------
function Word 
Fixed_state::get_srr0();
	return srr0;
endfunction
//---------------------------------------------------------------------------
function Word 
Fixed_state::get_srr1();
	return srr1;
endfunction
//---------------------------------------------------------------------------
function Word 
Fixed_state::get_csrr0();
	return csrr0;
endfunction
//---------------------------------------------------------------------------
function Word 
Fixed_state::get_csrr1();
	return csrr1;
endfunction
//---------------------------------------------------------------------------
function Word 
Fixed_state::get_mcsrr0();
	return mcsrr0;
endfunction
//---------------------------------------------------------------------------
function Word 
Fixed_state::get_mcsrr1();
	return mcsrr1;
endfunction
//---------------------------------------------------------------------------
function Msr 
Fixed_state::get_msr();
	return msr;
endfunction
//---------------------------------------------------------------------------
function Esr 
Fixed_state::get_esr();
	return esr;
endfunction
//---------------------------------------------------------------------------
function Word 
Fixed_state::get_dear();
	return dear;
endfunction
//---------------------------------------------------------------------------
function Word
Fixed_state::get_gout();
	return gout;
endfunction
//---------------------------------------------------------------------------
function Word
Fixed_state::get_goe();
	return goe;
endfunction
//---------------------------------------------------------------------------
function Word
Fixed_state::get_mem(input Address address);
	return mem_model.get(address);
endfunction
//---------------------------------------------------------------------------
function bit
Fixed_state::get_mem_first(ref Address iter, output Word data);
	return mem_model.iter_first(iter, data);
endfunction
//---------------------------------------------------------------------------
function bit
Fixed_state::get_mem_next(ref Address iter, output Word data);
	return mem_model.iter_next(iter, data);
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_pc(input Address p);
	pc = p;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_gpr(input int index, Word w);
	gpr[index] = w;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_cr(input int index, Cr_field c);
	cr[index] = c;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_ctr(input Word c);
	ctr = c;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_lnk(input Word l);
	lnk = l;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_xer(input Word x);
	xer = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_srr0(input Word x);
	srr0 = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_srr1(input Word x);
	srr1 = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_csrr0(input Word x);
	csrr0 = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_csrr1(input Word x);
	csrr1 = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_mcsrr0(input Word x);
	mcsrr0 = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_mcsrr1(input Word x);
	mcsrr1 = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_esr(input Esr x);
	esr = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_dear(input Word x);
	dear = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_msr(input Msr x);
	msr = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_gout(input Word x);
	gout = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_goe(input Word x);
	goe = x;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_mem(input int address, Word w);
	mem_model.set(address, w);
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_mem_model(ref Mem_model model);
	mem_model = model;
endfunction
//---------------------------------------------------------------------------
function Mem_model
Fixed_state::get_mem_model();
	return mem_model;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_io_model(ref Mem_model model);
	io_model = model;
endfunction
//---------------------------------------------------------------------------
function Mem_model
Fixed_state::get_io_model();
	return io_model;
endfunction
//---------------------------------------------------------------------------
function Nve_sstate
Fixed_state::get_nve_sstate();
	return nve_sstate;
endfunction
//---------------------------------------------------------------------------
function Nve_lut   
Fixed_state::get_nve_lut(input int num);
	return nve_lut[num];
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::set_nve_sstate(input Nve_sstate sstate);
	nve_sstate = sstate;
endfunction
//---------------------------------------------------------------------------
function void 
Fixed_state::set_nve_lut(input int num, Nve_lut lut);
	nve_lut[num] = lut;
endfunction
//---------------------------------------------------------------------------
function void
Fixed_state::copy_from(input State a);
	Address iter;
	Word data;

	pc = a.get_pc();
	ctr = a.get_ctr();
	lnk = a.get_lnk();
	srr0 = a.get_srr0();
	srr1 = a.get_srr1();
	csrr0 = a.get_csrr0();
	csrr1 = a.get_csrr1();
	mcsrr0 = a.get_mcsrr0();
	mcsrr1 = a.get_mcsrr1();
	esr = a.get_esr();
	msr = a.get_msr();
	dear = a.get_dear();

	for(int i=0; i<32; i++) gpr[i] = a.get_gpr(i);
	for(int i=0; i<8; i++) cr[i] = a.get_cr(i);

	xer = a.get_xer();
	gout = a.get_gout();
	goe = a.get_goe();

	if( a.get_mem_first(iter, data) )
		do
			mem_model.set(iter, data);
		while( a.get_mem_next(iter, data) );

	nve_sstate = a.get_nve_sstate();
	for(int i=0; i<NUM_NVE_LUT; i++)
		nve_lut[i] = a.get_nve_lut(i);

endfunction


`endif

