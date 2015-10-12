// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef RAND_STATE__
`define RAND_STATE__

`include "state.sv"

//---------------------------------------------------------------------------
class Rand_state extends State;
	rand Address  pc;
	rand Word     gpr[0:31];
	rand Cr_field cr[0:7];
	rand Word     ctr;
	rand Word     lnk;
	rand Word     xer;
	rand Msr      msr;
	rand Esr      esr;
	rand Word     srr0, srr1;
	rand Word     csrr0, csrr1;
	rand Word     mcsrr0, mcsrr1;
	rand Word     dear;
	rand Word     gout;
	rand Word     goe;
	rand Nve_sstate nve_sstate;
	rand Nve_lut  nve_lut[NUM_NVE_LUT];

	Mem_model     mem_model;
	Mem_model     io_model;
	//Word          mem[int];
	const int     addr_space_size;  // used to bias ctr,lnk,srr0,csrr0,mcsrr0
	const int     io_space_size;


	rand int      r_seed;    // seed for random memory filling

	constraint xer_reserved_bits {
		xer[28:0] == '0;
	}

	constraint msr_reserved_bits {
		msr.comp_mode == 1'b0;  // always in 32bit mode
		msr.pr == 1'b0;         // always privileged
		msr.fp == 1'b0;         // no floating point
		msr.reserved0 == '0;
		msr.reserved1 == '0;
		msr.reserved2 == '0;
		msr.reserved3 == '0;
		msr.reserved4 == '0;
	}

	constraint esr_reserved_bits {
		esr.dlk == '0;
		esr.reserved0 == '0;
		esr.reserved1 == '0;
		esr.reserved2 == '0;
		esr.reserved3 == '0;
		esr.reserved4 == '0;
	}

	constraint bias_gpr_values {
		foreach(gpr[i]) 
			gpr[i] dist { 
				32'h80000000 := 1,
				32'h7fffffff := 1,
				32'h00000000 := 1,
				32'hffffffff := 1,
				[ 0 : 32'hffffffff ] :/ 10
			};
	}

	constraint bias_ctr    { ctr < addr_space_size; }
	constraint bias_lnk    { lnk < addr_space_size; }
	constraint bias_srr0   { srr0 < addr_space_size; }
	constraint bias_csrr0  { csrr0 < addr_space_size; }
	constraint bias_mcsrr0 { mcsrr0 < addr_space_size; }

	extern function new(input Mem_model _mem_model,
		Mem_model _io_model,
		input int addr_space_size = 2**32,
		input int io_space_size = 2**32);

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

	extern virtual function void       set_mem_model(ref Mem_model model);
	extern virtual function Mem_model  get_mem_model();

	extern virtual function void       set_io_model(ref Mem_model model);
	extern virtual function Mem_model  get_io_model();

	extern virtual function void       clear_mem(input Address last);

	extern virtual function Nve_sstate get_nve_sstate();
	extern virtual function Nve_lut    get_nve_lut(input int num);
	extern virtual function void       set_nve_sstate(input Nve_sstate sstate);
	extern virtual function void       set_nve_lut(input int num, Nve_lut lut);
endclass
//---------------------------------------------------------------------------
function 
Rand_state::new(Mem_model _mem_model,
		Mem_model _io_model,
		input int addr_space_size = 2**32,
		input int io_space_size = 2**32);
	mem_model = _mem_model;
	io_model = _io_model;
	this.addr_space_size = addr_space_size;
	this.io_space_size = io_space_size;
endfunction
//---------------------------------------------------------------------------
function Address
Rand_state::get_pc();
	return pc;
endfunction
//---------------------------------------------------------------------------
function Word
Rand_state::get_gpr(input int index);
	return gpr[index];
endfunction
//---------------------------------------------------------------------------
function Cr_field
Rand_state::get_cr(input int index);
	return cr[index];
endfunction
//---------------------------------------------------------------------------
function Word
Rand_state::get_ctr();
	return ctr;
endfunction
//---------------------------------------------------------------------------
function Word
Rand_state::get_lnk();
	return lnk;
endfunction
//---------------------------------------------------------------------------
function Word
Rand_state::get_xer();
	return xer;
endfunction
//---------------------------------------------------------------------------
function Word 
Rand_state::get_srr0();
	return srr0;
endfunction
//---------------------------------------------------------------------------
function Word 
Rand_state::get_srr1();
	return srr1;
endfunction
//---------------------------------------------------------------------------
function Word 
Rand_state::get_csrr0();
	return csrr0;
endfunction
//---------------------------------------------------------------------------
function Word 
Rand_state::get_csrr1();
	return csrr1;
endfunction
//---------------------------------------------------------------------------
function Word 
Rand_state::get_mcsrr0();
	return mcsrr0;
endfunction
//---------------------------------------------------------------------------
function Word 
Rand_state::get_mcsrr1();
	return mcsrr1;
endfunction
//---------------------------------------------------------------------------
function Msr 
Rand_state::get_msr();
	return msr;
endfunction
//---------------------------------------------------------------------------
function Esr 
Rand_state::get_esr();
	return esr;
endfunction
//---------------------------------------------------------------------------
function Word 
Rand_state::get_dear();
	return dear;
endfunction
//---------------------------------------------------------------------------
function Word
Rand_state::get_gout();
	return gout;
endfunction
//---------------------------------------------------------------------------
function Word
Rand_state::get_goe();
	return goe;
endfunction
//---------------------------------------------------------------------------
function Word
Rand_state::get_mem(input Address address);
	return mem_model.get(address);
endfunction
//---------------------------------------------------------------------------
function bit
Rand_state::get_mem_first(ref Address iter, output Word data);
	return mem_model.iter_first(iter, data);
endfunction
//---------------------------------------------------------------------------
function bit
Rand_state::get_mem_next(ref Address iter, output Word data);
	return mem_model.iter_next(iter, data);
endfunction
//---------------------------------------------------------------------------
function void
Rand_state::set_mem_model(ref Mem_model model);
	mem_model = model;	
endfunction
//---------------------------------------------------------------------------
function Mem_model
Rand_state::get_mem_model();
	return mem_model;
endfunction
//---------------------------------------------------------------------------
function void
Rand_state::set_io_model(ref Mem_model model);
	io_model = model;	
endfunction
//---------------------------------------------------------------------------
function Mem_model
Rand_state::get_io_model();
	return io_model;
endfunction
//---------------------------------------------------------------------------
function void
Rand_state::clear_mem(input Address last);
	mem_model.clear(last);
endfunction
//---------------------------------------------------------------------------
function Nve_sstate
Rand_state::get_nve_sstate();
	return nve_sstate;
endfunction
//---------------------------------------------------------------------------
function Nve_lut   
Rand_state::get_nve_lut(input int num);
	return nve_lut[num];
endfunction
//---------------------------------------------------------------------------
function void
Rand_state::set_nve_sstate(input Nve_sstate sstate);
	nve_sstate = sstate;
endfunction
//---------------------------------------------------------------------------
function void 
Rand_state::set_nve_lut(input int num, Nve_lut lut);
	nve_lut[num] = lut;
endfunction
//---------------------------------------------------------------------------
`endif

/* vim: set noet fenc= ff=unix sts=0 sw=8 ts=4 : */
