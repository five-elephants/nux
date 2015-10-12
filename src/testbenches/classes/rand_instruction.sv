// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef RAND_INSTRUCTION__
`define RAND_INSTRUCTION__

`include "instruction.sv"

typedef enum int {
	Form_d = 0,
	Form_xo = 1,
	Form_i = 2,
	Form_b = 3,
	Form_xl = 4,
	Form_x = 5,
	Form_m = 6,
	Form_xfx = 7
} Op_form;


class Rand_instruction extends Instruction;
	State state;
	const bit no_branches;
	const bit no_wait;
	const bit no_exceptions;

	const int addr_space_size;

	rand Op_form op_form;
	rand Opcd opcd;
	rand logic[4:0] ra;
	rand logic[4:0] rb;
	rand logic[4:0] rt;
	rand logic[15:0] d;

	rand logic oe;
	rand logic rc;
	rand Xo_opcd xo;

	rand logic[23:0] li;
	rand logic       aa;
	rand logic       lk;

	rand logic[4:0]  bo;
	rand logic[4:0]  bi;
	rand logic[13:0] bd;

	rand logic[4:0]  bt;
	rand logic[4:0]  ba;
	rand logic[4:0]  bb;
	rand Xl_opcd     xxo;

	rand X_opcd      x_xo;

	rand logic[4:0]  mb;
	rand logic[4:0]  me;

	rand Xfx_opcd    xfx_xo;
	//rand logic[9:0]  spr;
	rand Spr_index  spr;
	rand int        fxm_i;
	rand bit        one_crf_form;

	/*constraint tmp_no_mul {
		(xo != Xop_mulhw)
		&& (xo != Xop_mulhwu)
		&& (xo != Xop_mullw);
	}*/

	constraint dont_select_branches {
		//if( no_branches == 1'b1 )
			op_form != Form_i
			&& op_form != Form_b
			&& op_form != Form_xl;
	}

	constraint no_wait_instruction {
		//if( no_wait == 1'b1 )
			x_xo != Xop_wait;
	}

	constraint avoid_exceptions {
		if( op_form == Form_d )
			opcd != Op_twi;

		if( opcd == Op_alu_xo )
			x_xo != Xop_tw;
	}

	constraint opcd_subset {
		solve op_form before opcd;

		if( op_form == Form_d )
			opcd inside { Op_addi, Op_addis, Op_andi, Op_andis, Op_ori, Op_oris, 
			              Op_xori, Op_xoris, Op_addic, Op_addic_rec, Op_subfic,
			              Op_lwz, Op_stw, Op_cmpi, Op_cmpli, Op_lbz, Op_lhz,
						  Op_stb, Op_sth, Op_lwzu, Op_stwu, Op_lbzu, Op_lhzu,
			              Op_stbu, Op_sthu, Op_mulli, 
						  Op_lmw, Op_stmw, Op_twi, Op_nvecmpi };
		else if( op_form == Form_xo )
			opcd inside { Op_alu_xo };
		else if( op_form == Form_x )
			opcd inside { Op_nve_xo, Op_alu_xo };
		else if( op_form == Form_i )
			opcd inside { Op_branch };
		else if( op_form == Form_b )
			opcd inside { Op_bc };
		else if( op_form == Form_xl )
			opcd inside { Op_bclr };
		else if( op_form == Form_m )
			opcd inside { Op_rlwimi, Op_rlwinm, Op_rlwnm };
		else if( op_form == Form_xfx )
			opcd inside { Op_alu_xo };
	}

	constraint only_valid_nve_combinations {
		if( opcd == Op_alu_xo || opcd == Op_bclr ) {
			!(x_xo inside { Xop_nvem, Xop_nves, Xop_nvemtl });
		}

		if( opcd == Op_nve_xo ) {
			x_xo inside { Xop_nvem, Xop_nves, Xop_nvemtl };
		}
	}
	
	constraint no_synapse_instructions {
		!(opcd inside { Op_syncmpi, Op_syncmpi_rec });
		!(x_xo inside {
			Xop_synm   ,
			Xop_syns   ,
			Xop_synmtl ,
			Xop_synmtvr,
			Xop_synmfvr,
			Xop_synmtp ,
			Xop_synmfp ,
			Xop_synmvvr,
			Xop_synops ,
			Xop_synswp 
		});
	}

	constraint nve_lut_limit {
		if( opcd == Op_nve_xo && x_xo == Xop_nvem )
			rb < NUM_NVE_LUT;

		if( opcd == Op_nve_xo && x_xo == Xop_nvemtl )
			rt < NUM_NVE_LUT;
	}


	// it is not allowed to decrement the counter when simultaneously decrementing it
	constraint bcctr_and_decrement {
		solve opcd,xxo before bt;
		if( opcd == Op_bclr && xxo == Xxop_bcctr )
			bt[2] == 1'b1;
	}

	constraint mem_multiple_ra_rt {
		solve opcd before rt,ra;

		if( opcd == Op_lmw || opcd == Op_stmw ) {
			rt > ra;
		}
	}

	// load/store with update instructions may not have ra == 0 or ra == rt
	constraint load_store_with_update {
		if( opcd == Op_lwzu || opcd == Op_lhzu || opcd == Op_lhau || opcd == Op_lbzu
				|| opcd == Op_stwu || opcd == Op_sthu || opcd == Op_stbu
				|| (opcd == Op_alu_xo && x_xo == Xop_lwzux)
				|| (opcd == Op_alu_xo && x_xo == Xop_lhzux)
				|| (opcd == Op_alu_xo && x_xo == Xop_lhaux)
				|| (opcd == Op_alu_xo && x_xo == Xop_lbzux)
				|| (opcd == Op_alu_xo && x_xo == Xop_stwux)
				|| (opcd == Op_alu_xo && x_xo == Xop_sthux)
				|| (opcd == Op_alu_xo && x_xo == Xop_stbux) )
		{
			ra != rt;
			ra != 0;
		}
	}

	constraint fxm_i_limits {
		fxm_i > 0 && fxm_i < 8;
	}

	constraint only_some_sprs {
		spr inside { 
			Spr_xer, Spr_lnk, Spr_ctr, Spr_srr0, Spr_srr1, Spr_csrr0, 
			Spr_csrr1, Spr_mcsrr0, Spr_mcsrr1, Spr_dec, Spr_decar,
			Spr_dear, Spr_esr, Spr_tsr, Spr_tcr, Spr_tbu, Spr_tbl,
			Spr_gin, Spr_gout, Spr_goe
		};
	}
	
	function Word rai0(Reg_index ra);
		if( ra == 0 )
			return '0;
		else
			return state.get_gpr(ra);
	endfunction

	// load/store instructions may not generate unaligned EAs
	constraint align_load_store {
		if( opcd inside { Op_lwz, Op_lwzu, Op_stw, Op_stwu, Op_lmw, Op_stmw } ) {
			(rai0(ra) + { {16{d[15]}}, d }) % 4 == 0;
		} else if( (opcd == Op_alu_xo) && (x_xo inside { Xop_lwzx, Xop_lwzux, Xop_stwx, Xop_stwux }) ) {
			(rai0(ra) + state.get_gpr(rb)) % 4 == 0;
		}

		if( opcd inside { Op_lhz, Op_lhzu, Op_lha, Op_lhau, Op_sth, Op_sthu } ) {
			(rai0(ra) + { {16{d[15]}}, d }) % 2 == 0;
		} else if( (opcd == Op_alu_xo) && (x_xo inside { Xop_lhzx, Xop_lhzux, Xop_lhax, Xop_lhaux, Xop_sthx, Xop_sthux }) ) {
			(rai0(ra) + state.get_gpr(rb)) % 2 == 0;
		}
	}

	// external control instructions must be word aligned
	constraint align_external_control {
		if( opcd == Op_alu_xo ) {
			if( x_xo inside { Xop_ecowx, Xop_eciwx } ) {
				(rai0(ra) + state.get_gpr(rb)) % 4 == 0;
			}
		}
	}

	constraint no_xop_xo_null { xo != Xop_xo_null; }
	constraint no_xop_xfx_null { xfx_xo != Xop_xfx_null; }


	/** Branches may only branch to addresses within the address space. */
	constraint addr_space_limitation {
		solve opcd,xxo,aa before li,bd;

		// branch instructions
		if( opcd == Op_branch ) {
			aa -> ({ {8{li[23]}}, li } < addr_space_size);
			!aa -> (unsigned'(signed'(state.get_pc()) + signed'({ {8{li[23]}}, li })) < addr_space_size);
		}

		// branch conditional
		if( opcd == Op_bc ) {
			aa -> ({ {18{bd[13]}}, bd } < addr_space_size);
			!aa -> (unsigned'(signed'(state.get_pc()) + signed'({ {18{bd[13]}}, bd })) < addr_space_size);
		}

		// branch to link register
		if( (opcd == Op_bclr) && (xxo == Xxop_bclr) ) {
			(state.get_lnk() >> 2) < addr_space_size;
		}

		// branch to count register
		if( (opcd == Op_bclr) && (xxo == Xxop_bcctr) ) {
			(state.get_ctr() >> 2) < addr_space_size;
		}

		// return from interrupt instructions
		if( opcd == Op_bclr ) {
			(xxo == Xxop_rfi) -> ((state.get_srr0() >> 2) < addr_space_size);
			(xxo == Xxop_rfmci) -> ((state.get_mcsrr0() >> 2) < addr_space_size);
			(xxo == Xxop_rfci) -> ((state.get_csrr0() >> 2) < addr_space_size);
		}
	}
	//---------------------------------------------------------------------------

	function new(input State _state = null, 
			input bit _no_branches = 1'b0, 
				_no_wait = 1'b0, 
				_no_exceptions = 1'b0,
			input int addr_space_size = 1024 );
		state = _state;
		no_branches = _no_branches;
		no_wait = _no_wait;
		no_exceptions = _no_exceptions;
		this.addr_space_size = addr_space_size;
	endfunction

	function void set_state(const ref State s);
		state = s;
	endfunction

	function State get_state();
		return state;
	endfunction

	function void pre_randomize();
		if( state == null ) begin
			this.align_load_store.constraint_mode(0);
			this.addr_space_limitation.constraint_mode(0);
		end

		if( !no_exceptions ) begin
			this.avoid_exceptions.constraint_mode(0);
			this.align_load_store.constraint_mode(0);
		end
		if( !no_wait )
			this.no_wait_instruction.constraint_mode(0);
		if( !no_branches )
			this.dont_select_branches.constraint_mode(0);
	endfunction

	// interface from Instruction
	extern virtual function Inst get();

	extern function Inst get_d_form();
	extern function Inst get_xo_form();
	extern function Inst get_i_form();
	extern function Inst get_b_form();
	extern function Inst get_xl_form();
	extern function Inst get_x_form();
	extern function Inst get_m_form();
	extern function Inst get_xfx_form();
endclass

//---------------------------------------------------------------------------
//constraint Rand_instruction::opcd_subset {
//	opcd dist { Op_addi, Op_addis, Op_andi, Op_andis, Op_ori, Op_oris, Op_xori, Op_xoris };
//}
//---------------------------------------------------------------------------
function Inst
Rand_instruction::get();
	Inst rv;

	case(op_form)
		Form_d:   rv = get_d_form();
		Form_xo:  rv = get_xo_form();
		Form_i:   rv = get_i_form();
		Form_b:   rv = get_b_form();
		Form_xl:  rv = get_xl_form();
		Form_x:   rv = get_x_form();
		Form_m:   rv = get_m_form();
		Form_xfx: rv = get_xfx_form();

		default:  rv = get_d_form();
	endcase

	return rv;
endfunction
//---------------------------------------------------------------------------
function Inst
Rand_instruction::get_d_form();
	Inst d_form;

	d_form.d.opcd = opcd;
	d_form.d.ra = ra;
	d_form.d.rt = rt;
	d_form.d.d = d;

	return d_form;
endfunction
//---------------------------------------------------------------------------
function Inst
Rand_instruction::get_xo_form();
	Inst xo_form;

	xo_form.xo.opcd = opcd;
	xo_form.xo.ra = ra;
	xo_form.xo.rt = rt;
	xo_form.xo.rb = rb;
	xo_form.xo.xo = xo;
	xo_form.xo.oe = oe;
	xo_form.xo.rc = rc;

	return xo_form;
endfunction
//---------------------------------------------------------------------------
function Inst
Rand_instruction::get_i_form();
	Inst i_form;

	i_form.i.opcd = opcd;
	i_form.i.li = li;
	i_form.i.aa = aa;
	i_form.i.lk = lk;

	return i_form;
endfunction
//---------------------------------------------------------------------------
function Inst
Rand_instruction::get_b_form();
	Inst b_form;

	b_form.b.opcd = opcd;
	b_form.b.bo = bo;
	b_form.b.bi = bi;
	b_form.b.bd = bd;
	b_form.b.aa = aa;
	b_form.b.lk = lk;

	return b_form;
endfunction
//---------------------------------------------------------------------------
function Inst
Rand_instruction::get_xl_form();
	Inst xl_form;

	xl_form.xl.opcd = opcd;
	xl_form.xl.bt = bt;
	xl_form.xl.ba = ba;
	xl_form.xl.bb = bb;
	xl_form.xl.xo = xxo;
	xl_form.xl.lk = lk;

	return xl_form;
endfunction
//---------------------------------------------------------------------------
function Inst
Rand_instruction::get_x_form();
	Inst x_form;

	x_form.x.opcd = opcd;
	x_form.x.rt = rt;
	x_form.x.ra = ra;
	x_form.x.rb = rb;
	x_form.x.xo = x_xo;
	x_form.x.rc = rc;

	return x_form;
endfunction
//---------------------------------------------------------------------------
function Inst
Rand_instruction::get_m_form();
	Inst m_form;

	m_form.m.opcd = opcd;
	m_form.m.rs = rt;
	m_form.m.ra = ra;
	m_form.m.rb = rb;
	m_form.m.mb = mb;
	m_form.m.me = me;
	m_form.m.rc = rc;

	return m_form;
endfunction
//---------------------------------------------------------------------------
function Inst
Rand_instruction::get_xfx_form();
	Inst xfx_form;

	xfx_form.xfx.opcd = opcd;
	xfx_form.xfx.rt = rt;

	if( xfx_xo == Xop_mtocrf || xfx_xo == Xop_mfocrf ) begin
		if( one_crf_form ) begin
			xfx_form.xfx.spr = 10'h0;
			xfx_form.xfx.spr[1 + fxm_i] = 1'b1;
			xfx_form.xfx.spr[9] = 1'b1;
		end else begin
			xfx_form.xfx.spr = {1'b0, spr[7:0], 1'b0};
		end
	end else
		xfx_form.xfx.spr = spr;

	xfx_form.xfx.xo = xfx_xo;
	xfx_form.xfx.not_used = 1'b0;

	return xfx_form;
endfunction
//---------------------------------------------------------------------------

`endif
