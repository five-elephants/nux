// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef STATE__
`define STATE__

`include "mem_model.sv"

import Pu_types::*;

virtual class State;
	pure virtual function Address    get_pc();
	pure virtual function Word       get_gpr(input int index);
	pure virtual function Cr_field   get_cr(input int index);
	pure virtual function Word       get_ctr();
	pure virtual function Word       get_lnk();
	pure virtual function Word       get_xer();
	pure virtual function Word       get_srr0();
	pure virtual function Word       get_srr1();
	pure virtual function Word       get_csrr0();
	pure virtual function Word       get_csrr1();
	pure virtual function Word       get_mcsrr0();
	pure virtual function Word       get_mcsrr1();
	pure virtual function Msr        get_msr();
	pure virtual function Esr        get_esr();
	pure virtual function Word       get_dear();
	pure virtual function Word       get_gout();
	pure virtual function Word       get_goe();
	pure virtual function Word       get_mem(input Address address);
	pure virtual function bit        get_mem_first(ref Address iter, output Word data);
	pure virtual function bit        get_mem_next(ref Address iter, output Word data);

	pure virtual function void       set_mem_model(ref Mem_model model);
	pure virtual function Mem_model  get_mem_model();

	pure virtual function void       set_io_model(ref Mem_model model);
	pure virtual function Mem_model  get_io_model();

	pure virtual function void       set_nve_sstate(input Nve_sstate sstate);
	pure virtual function Nve_sstate get_nve_sstate();
	pure virtual function void       set_nve_lut(input int num, Nve_lut lut);
	pure virtual function Nve_lut    get_nve_lut(input int num);
endclass

typedef struct {
	bit pc;
	bit gpr[32];
	bit cr[8];
	bit ctr;
	bit lnk;
	bit xer;
	bit srr0;
	bit srr1;
	bit csrr0;
	bit csrr1;
	bit mcsrr0;
	bit mcsrr1;
	bit msr;
	bit esr;
	bit dear;
	bit gout;
	bit goe;
	bit mem;
	bit io;
	bit nve_sstate;
	bit nve_lut;
} Cmp_ignore_mask;

//---------------------------------------------------------------------------
// Compare two State implementations for equality and return 1 if they are 
// equal.
//---------------------------------------------------------------------------
/*function automatic bit compare_state(input State a, State b);
	bit rv = 1;

	if( a.get_pc() !== b.get_pc() ) rv = 0;
	if( a.get_ctr() !== b.get_ctr() ) rv = 0;
	if( a.get_lnk() !== b.get_lnk() ) rv = 0;

	for(int i=0; i<32; i++)
		if( a.get_gpr(i) !== b.get_gpr(i) ) rv = 0;

	// only compare implemented CR fields (currently only one)
	for(int i=0; i<1; i++)
		if( a.get_cr(i) !== b.get_cr(i) ) rv = 0;

	if( a.get_xer() !== b.get_xer() ) rv = 0;

	return rv;
endfunction
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Compare two State implementations for equality and return 1 if they are 
// equal.
//---------------------------------------------------------------------------
function automatic bit compare_state_igpc(input State a, State b);
	bit rv = 1;
	Xer tmp_xer;

	if( a.get_ctr() !== b.get_ctr() ) begin
		$warning("compare_state: failed at CTR (expecting '%h', got '%h')",
				a.get_ctr(), b.get_ctr());
		rv = 0;
	end

	if( a.get_lnk() !== b.get_lnk() ) begin
		$warning("compare_state: failed at LNK (expecting '%h', got '%h')",
				a.get_lnk(), b.get_lnk());
		rv = 0;
	end

	for(int i=0; i<32; i++) begin
		if( a.get_gpr(i) !== b.get_gpr(i) ) begin
			$warning("compare_state: failed at GPR%d", i);
			rv = 0;
		end
	end

	// only compare implemented CR fields (currently only one)
	for(int i=0; i<1; i++) begin
		if( a.get_cr(i) !== b.get_cr(i) ) begin
			$warning("compare_state: failed at CR%d (expecting '%b', got '%b')",
					i, a.get_cr(i), b.get_cr(i));
			rv = 0;
		end
	end

	if( a.get_xer() !== b.get_xer() ) begin
		tmp_xer = a.get_xer();
	//	$warning("compare_state: failed at XER (expecting SO=%b, OV=%b, CA=%b)",
	//			tmp_xer.so, tmp_xer.ov, tmp_xer.ca);
		$warning("compare_state: failed at XER (expecting '%b', got '%b')",
				a.get_xer(), b.get_xer());
	
		rv = 0;
	end

	return rv;
endfunction*/
//---------------------------------------------------------------------------
// wild inequality: wildcard bits are only used in expected
`define IS_NOT_EQUAL(expected, actual) (actual !=? expected)
`define IS_EQUAL(expected, actual) (actual ==? expected)

function automatic bit check_x(input Word w);
	foreach(w[i])
		if( (w[i] === 1'bx) || (w[i] === 1'bz) )
			return 1'b0;

	return 1'b1;
endfunction
//---------------------------------------------------------------------------
// Compare two State implementations for equality and return 1 if they are 
// equal.
//
// This version uses an ignore mask to selectively disable comparison of
// single fields.
//---------------------------------------------------------------------------
function automatic bit compare_state_masked(input State a, State b, Cmp_ignore_mask mask);
	bit rv = 1;
	Xer tmp_xer;

	if( !mask.pc )
		cmp_pc: assert(`IS_EQUAL(a.get_pc() ,  b.get_pc()) && check_x(b.get_pc())) else begin
			$warning("compare_state: failed at PC (expecting '%h', got '%h')",
					a.get_pc(), b.get_pc());
			rv = 0;
		end

	if( !mask.ctr )
		cmp_ctr: assert(`IS_EQUAL(a.get_ctr() ,  b.get_ctr()) && check_x(b.get_ctr())) else begin
			$warning("compare_state: failed at CTR (expecting '%h', got '%h')",
					a.get_ctr(), b.get_ctr());
			rv = 0;
		end

	if( !mask.lnk )
		cmp_lnk: assert(`IS_EQUAL(a.get_lnk() ,  b.get_lnk()) && check_x(b.get_lnk()) ) else begin
			$warning("compare_state: failed at LNK (expecting '%h', got '%h')",
					a.get_lnk(), b.get_lnk());
			rv = 0;
		end

	if( !mask.srr0 )
		cmp_srr0: assert(`IS_EQUAL(a.get_srr0() ,  b.get_srr0()) && check_x(b.get_srr0()) ) else begin
			$warning("compare_state: failed at SRR0 (expecting '%h', got '%h')",
					a.get_srr0(), b.get_srr0());
			rv = 0;
		end

	if( !mask.srr1 )
		cmp_srr1: assert(`IS_EQUAL(a.get_srr1() ,  b.get_srr1()) && check_x(b.get_srr1())) else begin
			$warning("compare_state: failed at SRR1 (expecting '%h', got '%h')",
					a.get_srr1(), b.get_srr1());
			rv = 0;
		end
	
	if( !mask.csrr0 )
		cmp_csrr0: assert(`IS_EQUAL(a.get_csrr0() ,  b.get_csrr0()) && check_x(b.get_csrr0()) ) else begin
			$warning("compare_state: failed at CSRR0 (expecting '%h', got '%h')",
					a.get_csrr0(), b.get_csrr0());
			rv = 0;
		end
	
	if( !mask.csrr1 )
		cmp_csrr1: assert(`IS_EQUAL(a.get_csrr1() ,  b.get_csrr1()) && check_x(b.get_csrr1()) ) else begin
			$warning("compare_state: failed at CSRR1 (expecting '%h', got '%h')",
					a.get_csrr1(), b.get_csrr1());
			rv = 0;
		end
	
	if( !mask.mcsrr0 )
		cmp_mcsrr0: assert(`IS_EQUAL(a.get_mcsrr0() ,  b.get_mcsrr0()) && check_x(b.get_mcsrr0()) ) else begin
			$warning("compare_state: failed at MCSRR0 (expecting '%h', got '%h')",
					a.get_mcsrr0(), b.get_mcsrr0());
			rv = 0;
		end
	
	if( !mask.mcsrr1 )
		cmp_mcsrr1: assert(`IS_EQUAL(a.get_mcsrr1() ,  b.get_mcsrr1()) && check_x(b.get_mcsrr1()) ) else begin
			$warning("compare_state: failed at MCSRR1 (expecting '%h', got '%h')",
					a.get_mcsrr1(), b.get_mcsrr1());
			rv = 0;
		end
	
	if( !mask.msr )
		cmp_msr: assert(`IS_EQUAL(a.get_msr() ,  b.get_msr()) && check_x(b.get_msr())) else begin
			$warning("compare_state: failed at MSR (expecting '%h', got '%h')",
					a.get_msr(), b.get_msr());
			rv = 0;
		end
	
	if( !mask.esr )
		cmp_esr: assert(`IS_EQUAL(a.get_esr() ,  b.get_esr()) && check_x(b.get_esr()) ) else begin
			$warning("compare_state: failed at ESR (expecting '%h', got '%h')",
					a.get_esr(), b.get_esr());
			rv = 0;
		end
	
	if( !mask.dear )
		cmp_dear: assert(`IS_EQUAL(a.get_dear() ,  b.get_dear()) && check_x(b.get_dear()) ) else begin
			$warning("compare_state: failed at DEAR (expecting '%h', got '%h')",
					a.get_dear(), b.get_dear());
			rv = 0;
		end

	if( !mask.gout )
		cmp_gout: assert(`IS_EQUAL(a.get_gout() ,  b.get_gout()) && check_x(b.get_gout()) ) else begin
			$warning("compare_state: failed at GOUT (expecting '%h', got '%h')",
					a.get_gout(), b.get_gout());
			rv = 0;
		end

	if( !mask.goe )
		cmp_goe: assert(`IS_EQUAL(a.get_goe(), b.get_goe()) && check_x(b.get_goe())) else begin
			$warning("compare_state: failed at GOE (expecting '%h', got '%h')",
					a.get_goe(), b.get_goe());
			rv = 0;
		end

	for(int i=0; i<32; i++) begin
		if( !mask.gpr[i] )
			cmp_gpr: assert(`IS_EQUAL(a.get_gpr(i) ,  b.get_gpr(i)) && check_x(b.get_gpr(i)) ) else begin
				$warning("compare_state: failed at GPR%d, (expecting '%h', got '%h')",
				         i, a.get_gpr(i), b.get_gpr(i));
				rv = 0;
			end
	end

	// compare CR fields
	for(int i=0; i<8; i++) begin
		if( !mask.cr[i] )
			cmp_cr: assert(`IS_EQUAL(a.get_cr(i) ,  b.get_cr(i)) && check_x(b.get_cr(i)) ) else begin
				$warning("compare_state: failed at CR%d (expecting '%b', got '%b')",
						i, a.get_cr(i), b.get_cr(i));
				rv = 0;
			end
	end

	if( !mask.xer )
		cmp_xer: assert(`IS_EQUAL(a.get_xer() ,  b.get_xer()) && check_x(b.get_xer()) ) else begin
			tmp_xer = a.get_xer();
		//	$warning("compare_state: failed at XER (expecting SO=%b, OV=%b, CA=%b)",
		//			tmp_xer.so, tmp_xer.ov, tmp_xer.ca);
			$warning("compare_state: failed at XER (expecting '%b', got '%b')",
					a.get_xer(), b.get_xer());
		
			rv = 0;
		end

	if( !mask.mem ) begin
		Address iter;
		Word tmp;

		if( a.get_mem_first(iter, tmp) )
			do
				cmp_mem: assert(`IS_EQUAL(tmp ,  b.get_mem(iter)) && check_x(b.get_mem(iter)) ) else begin
					$warning("compare_state: failed at mem address %d (expecting '%h', got '%h')",
							iter, tmp, b.get_mem(iter));
					rv = 0;
				end
			while( a.get_mem_next(iter, tmp) );

		if( b.get_mem_first(iter, tmp) )
			do
				cmp_mem_2: assert(`IS_EQUAL(tmp ,  a.get_mem(iter)) && check_x(a.get_mem(iter)) ) else begin
					$warning("compare_state: failed at mem address %d in pass 2 (expecting '%h', got '%h')",
							iter, a.get_mem(iter), tmp);
					rv = 0;
				end
			while( b.get_mem_next(iter, tmp) );
	end

	if( !mask.io ) begin
		Address iter;
		Word tmp;
		Mem_model io_a, io_b;

		io_a = a.get_io_model();
		io_b = b.get_io_model();

		if( io_a.iter_first(iter, tmp) )
			do
				cmp_io: assert(`IS_EQUAL(tmp,  io_b.get(iter)) && check_x(io_b.get(iter)) ) else begin
					$warning("compare_state: failed at IO address %d (expecting '%h', got '%h')",
							iter, tmp, io_b.get(iter));
					rv = 0;
				end
			while( io_a.iter_next(iter, tmp) );

		if( io_b.iter_first(iter, tmp) )
			do
				cmp_io_2: assert(`IS_EQUAL(tmp ,  io_a.get(iter)) && check_x(io_a.get(iter)) ) else begin
					$warning("compare_state: failed at mem address %d in pass 2 (expecting '%h', got '%h')",
							iter, io_a.get(iter), tmp);
					rv = 0;
				end
			while( io_b.iter_next(iter, tmp) );
	end

	if( !mask.nve_sstate ) begin
		Nve_sstate as, bs;

		as = a.get_nve_sstate();
		bs = b.get_nve_sstate();

		cmp_nve_sstate: assert(`IS_EQUAL(as, bs) && check_x(bs)) else begin
			$warning("compare_state: failed at nve_sstate (expecting '%h', got '%h'",
			as, bs);
			rv = 0;
		end
	end


	if( !mask.nve_lut ) begin
		for(int i=0; i<NUM_NVE_LUT; i++) begin
			Nve_lut al, bl;

			al = a.get_nve_lut(i);
			bl = b.get_nve_lut(i);

			cmp_nve_lut: assert(`IS_EQUAL(al, bl) && check_x(bl)) else begin
				$warning("compare_state: failed at nve_lut (expecting '%h', got '%h'",
				al, bl);
				rv = 0;
			end
		end
	end

	return rv;
endfunction
//---------------------------------------------------------------------------

`undef IS_NOT_EQUAL
`undef IS_EQUAL

`endif

/* vim: set noet fenc= ff=unix sts=0 sw=8 ts=2 : */
