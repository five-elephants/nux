// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Decode_single
	(	input logic clk,
		input logic reset,

		Decode_ctrl_if.decode         ctrl,
		Decode_data_if.decode         data,

		Register_file_if.read         register_file,

		output Control_word           cw
	);

import Pu_types::*;
import Pu_inst::*;


logic          active;

logic          alu_en, branch_en;
Alu_op         alu_op;
logic[4:0]     alu_crl_ba;
logic[4:0]     alu_crl_bb;
logic[4:0]     alu_crl_bt;

Cr_op          cr_op;

Func_unit      fxdp_sel;

logic          br_jump;
logic[4:0]     br_crbi;
logic          br_cond;
logic          br_mask_cond;
logic          br_ctr_eq;
logic          br_mask_ctr;
logic          br_dec_ctr;
logic          br_save_lnk;
logic          br_to_lnk;
logic          br_to_ctr;

logic          trap_en;
Trap_to        trap_to;

logic          ls_en;
logic          ls_we;
Load_mode      ls_mode;

Reg_index      wb_gpr_dest_alu;
Reg_index      wb_gpr_dest_mem;
logic          wb_gpr_wr_alu;
logic          wb_gpr_wr_mem;
logic          wb_wr_cr;
logic[7:0]     wb_record_cr;
logic          wb_record_ca;
logic          wb_record_ov;
Address        wb_lnk;
logic[7:0]     wb_src_cr;
Register_move  wb_reg_mv;
logic          wb_spr_we;
logic[9:0]     wb_spr_sel;
logic          wb_msr_we;
logic          wb_sleep;

logic          if_hold;
logic          if_wait;
logic          is_nop;
logic          ra_is_zero;
logic          write_xer;

logic          cw_write_xer, cw_read_xer;
logic[7:0]     cw_write_cr, cw_read_cr_0, cw_read_cr_1, cw_read_cr_2;
logic          cw_read_ctr, cw_write_ctr;
logic          cw_read_lnk, cw_write_lnk;
Reg_index      cw_gpr_a, cw_gpr_b, cw_gpr_c;
logic          cw_read_gpr_a, cw_read_gpr_b, cw_read_gpr_c;
logic          cw_read_spr, cw_write_spr;
logic          cw_read_spr2;
Spr_reduced    cw_spr_src, cw_spr_dest;
Spr_reduced    cw_spr_src2;

logic          int_rest_base;
logic          int_rest_crit;
logic          int_rest_mcheck;
logic          int_block_external;

Ls_cycle_counter ls_ctr, next_ls_ctr;
logic[0:2]     sync_sreg;
logic          start_sync;


/** Detect, wether the instruction should be decoded by this module */
always_comb begin
	logic[15:0] cop;

	cop = {data.inst.x.opcd, data.inst.x.xo};
	unique casez(cop)
		{Op_lwzu, 10'bz}, {Op_lbzu, 10'bz}, {Op_lhzu, 10'bz},
		{Op_alu_xo, Xop_lbzux}, {Op_alu_xo, Xop_lhzux}, {Op_alu_xo, Xop_lwzux},
		{Op_lmw, 10'bz}, {Op_stmw, 10'bz},
		{Op_alu_xo, 1'bz, Xop_mulhwu}, {Op_alu_xo, 1'bz, Xop_mulhw},
		{Op_alu_xo, 1'bz, Xop_mullw}, {Op_mulli, 10'bz},
		{Op_alu_xo, 1'bz, Xop_divw},
		{Op_alu_xo, 1'bz, Xop_divwu}:
			active = 1'b0;
		default:
			active = 1'b1;
	endcase
end

//---------------------------------------------------------------------------
// enable functional blocks
//---------------------------------------------------------------------------
always_comb
begin : set_enables
	// defaults
	alu_en = 1'b0;
	branch_en = 1'b0;
	trap_en = 1'b0;
	ls_en = 1'b0;


	if( is_nop == 1'b0 ) begin
		unique case(data.inst.d.opcd)
			// ALU instructions
			Op_addi, Op_addis, Op_addic, Op_addic_rec,
			Op_ori, Op_oris, Op_andi, Op_andis, Op_xori, Op_xoris,
			Op_subfic, Op_rlwimi, Op_rlwinm, Op_rlwnm,
			Op_cmpi, Op_cmpli:
			begin
				alu_en = 1'b1;
			end
						
			Op_alu_xo: begin
				unique case(data.inst.x.xo)
					Xop_tw:
						trap_en = 1'b1;

					Xop_lwzx, Xop_lwzux,
					Xop_lhzx, Xop_lhzux,
					Xop_lbzx, Xop_lhzux,
					Xop_stwx, Xop_stwux,
					Xop_sthx, Xop_sthux,
					Xop_stbx, Xop_stbux:
					begin
						ls_en = 1'b1;
						alu_en = 1'b1;
					end

					default:
						alu_en = 1'b1;
				endcase
			end
			
			// branch instructions
			Op_bc, Op_branch:
			begin
				alu_en = 1'b1;
				branch_en = 1'b1;
			end

			Op_bclr:
			begin
				unique case(data.inst.xl.xo)
					Xxop_bclr, Xxop_bcctr, Xxop_rfi, Xxop_rfci, 
					Xxop_rfmci: begin
						alu_en = 1'b1;
						branch_en = 1'b1;
					end

					Xxop_mcrf: begin
						alu_en = 1'b0;
					end
					
					default:
						alu_en = 1'b1;
				endcase
			end

			// trap instructions
			Op_twi:
			begin
				trap_en = 1'b1;
			end

			// load/store instructions
			Op_lwz, Op_stw, Op_lbz, Op_stb, Op_lhz, Op_sth,
			Op_stwu, Op_stbu, Op_sthu:
			begin
				alu_en = 1'b1;
				ls_en = 1'b1;
			end

			default: begin
			end
		endcase
	end
end : set_enables

//---------------------------------------------------------------------------
// Hold instruction fetch
//---------------------------------------------------------------------------
always_comb begin
	logic[15:0] cop;

	// default assignments
	next_ls_ctr = ls_ctr;
	wb_sleep = 1'b0;
	if_wait = 1'b0;

	cop = {data.inst.x.opcd, data.inst.x.xo};
	unique casez(cop)
		// special wait instructions
		{Op_alu_xo, Xop_wait}: begin
			if( (data.inst.x.rt[1:0] == 2'b00) && (reset == 1'b0) && (ctrl.wakeup == 1'b0) ) begin
				wb_sleep = 1'b1;
        //if_hold = 1'b1;
        if_wait = 1'b1;
			end else
        //if_hold = 1'b0;
        if_wait = 1'b0;
		end

		// multi-cycle load/store instructions
		{Op_lwz, 10'bz}, {Op_lhz, 10'bz}, {Op_lbz, 10'bz},
		{Op_alu_xo, Xop_lwzx}, {Op_alu_xo, Xop_lhzx}, {Op_alu_xo, Xop_lbzx},
		{Op_stw, 10'bz}, {Op_stb, 10'bz}, {Op_sth, 10'bz},
		{Op_alu_xo, Xop_stwx}, {Op_alu_xo, Xop_sthx}, {Op_alu_xo, Xop_stbx},
		{Op_stwu, 10'bz}, {Op_stbu, 10'bz}, {Op_sthu, 10'bz},
		{Op_alu_xo, Xop_stwux}, {Op_alu_xo, Xop_sthux}, {Op_alu_xo, Xop_stbux}:
		begin
			if( ls_ctr == 0 ) begin
				if_hold = 1'b0;
				next_ls_ctr = LOAD_STORE_CYCLES;
			end else begin
				if_hold = 1'b1;
				next_ls_ctr = ls_ctr -1;
			end
		end

    default: begin
		if_hold = 1'b0;
		if_wait = 1'b0;
    end
	endcase
	/*if( data.inst.x.opcd == Op_alu_xo 
			&& data.inst.x.xo == Xop_wait 
			&& data.inst.x.rt[1:0] == 2'b00 
			&& reset == 1'b0 )
		if_hold = 1'b1;
	else
		if_hold = 1'b0;*/

  // hold instruction fetch when context sync in progress
  if_hold = (| sync_sreg);
end


always_ff @(posedge clk or posedge reset)
	if( reset )
		ls_ctr <= LOAD_STORE_CYCLES;
	else
		ls_ctr <= next_ls_ctr;

//---------------------------------------------------------------------------
// detect nops
//---------------------------------------------------------------------------
always_comb
begin : detect_nop
	if( (data.inst.d.opcd == Op_ori
			&& data.inst.d.ra == 0
			&& data.inst.d.rt == 0
			&& data.inst.d.d == 0)
		/*|| (data.inst.x.opcd == Op_alu_xo && data.inst.x.xo == Xop_wait)*/ )
	begin
		is_nop = 1'b1;
	end else begin
		is_nop = 1'b0;
	end
end : detect_nop

//---------------------------------------------------------------------------
// detect RA == 0 for instructions using RA|0
//---------------------------------------------------------------------------
always_comb 
	if( data.inst.d.ra == 0 ) 
		ra_is_zero = 1'b1;
	else
		ra_is_zero = 1'b0;


//---------------------------------------------------------------------------
// select register accesses
//---------------------------------------------------------------------------

// select the register fields in the instruction word to retrieve
// is now done statically one cycle earlier
/*always_comb
begin
	// default assignments
	cw_gpr_a = 5'b0;
	cw_gpr_b = 5'b0;
	cw_gpr_c = 5'b0;

	unique case(data.inst.d.opcd)
		// instructions using the RA and RS register fields
//		Op_stw, Op_stb, Op_sth:
//		begin
//			ctrl_data_hazard.gpr_a  = data.inst.xo.ra;
//			ctrl_data_hazard.gpr_b  = data.inst.xo.rt;
//		end
		
		// instructions using the RS and RA register fields (reversed order)
		Op_ori, Op_oris, Op_xori, Op_xoris, Op_andi, Op_andis, 
		Op_rlwimi:
		begin
			cw_gpr_a  = data.inst.d.rt;
			cw_gpr_b  = data.inst.xo.ra;
		end

		// instructions using RS and RB register fields
		Op_rlwinm, Op_rlwnm:
		begin
			cw_gpr_a  = data.inst.x.rt;
			cw_gpr_b  = data.inst.x.rb;
		end

		// instructions using RS and RB
		Op_alu_xo: begin
			unique case(data.inst.x.xo)
				Xop_and, Xop_andc, Xop_or, Xop_orc, Xop_xor, 
				Xop_nand, Xop_nor, Xop_eqv, Xop_extsb, Xop_extsh,
				Xop_slw, Xop_srw, Xop_srawi, Xop_sraw,
				Xop_popcb, Xop_prtyw, Xop_mfocrf, Xop_mtocrf,
				Xop_mtspr, Xop_mtmsr:
				begin
					cw_gpr_a  = data.inst.x.rt;
					cw_gpr_b  = data.inst.x.rb;
				end

				// instructions using the RA and RB register fields
				default: begin
					cw_gpr_a  = data.inst.d.ra;
					cw_gpr_b  = data.inst.xo.rb;
					cw_gpr_c  = data.inst.xo.rt;
				end
			endcase
		end

		// instructions using the RA and RB register fields
		default: begin
			cw_gpr_a  = data.inst.d.ra;
			cw_gpr_b  = data.inst.xo.rb;
			cw_gpr_c  = data.inst.xo.rt;
		end
	endcase
end*/

//---------------------------------------------------------------------------
// generate read and write signals for GPR
/*always_comb
begin
	logic[15:0] cop;

	// defaults
	cw_read_gpr_a = 1'b0;
	cw_read_gpr_b = 1'b0;
	cw_read_gpr_c = 1'b0;

	cop = {data.inst.x.opcd, data.inst.x.xo};

	if( !is_nop ) begin
		unique casez(cop)
			
			{Op_stw, 10'bz}, {Op_stb, 10'bz}, {Op_sth, 10'bz},
			{Op_stwu, 10'bz}, {Op_stbu, 10'bz}, {Op_sthu, 10'bz},
			{Op_addi, 10'bz}, {Op_addis, 10'bz}, {Op_lwz, 10'bz},
			{Op_lhz, 10'bz}, {Op_lbz, 10'bz},
			{Op_alu_xo, Xop_lwzx}, {Op_alu_xo, Xop_lwzx}, {Op_alu_xo, Xop_lbzx},
			{Op_alu_xo, Xop_stwx}, {Op_alu_xo, Xop_sthx}, {Op_alu_xo, Xop_stbx},
			{Op_alu_xo, Xop_stwux}, {Op_alu_xo, Xop_sthux}, {Op_alu_xo, Xop_stbux}:
				cw_read_gpr_a = ~ra_is_zero;

			// this should be every instruction that takes input from a GPR
			// and is not listed to read RA|0
			//{Op_cmpi, 10'bz}, {Op_cmpli, 10'bz}, {Op_addic, 10'bz},
			//{Op_addic_rec, 10'bz}, {Op_subfic, 10'bz}, {Op_andi, 10'bz},
			//{Op_andis, 10'bz}, {Op_ori, 10'bz}, {Op_oris, 10'bz},
			//{Op_xori, 10'bz}, {Op_xoris, 10'bz}, {Op_rlwinm, 10'bz},
			//{Op_rlwimi, 10'bz}, {Op_rlwnm, 10'bz},
			//{Op_alu_xo, 1'bz, Xop_add}, {Op_alu_xo, 1'bz, Xop_addc},
			//{Op_alu_xo, 1'bz, Xop_subf}, {Op_alu_xo, 1'bz, Xop_subfc},
			//{Op_alu_xo, 1'bz, Xop_adde}, {Op_alu_xo, 1'bz, Xop_subfe},
			//{Op_alu_xo, Xop_and}, {Op_alu_xo, Xop_andc}, {Op_alu_xo, Xop_or},
			//{Op_alu_xo, Xop_orc}, {Op_alu_xo, Xop_xor}, {Op_alu_xo, Xop_nand},
			//{Op_alu_xo, Xop_nor}, {Op_alu_xo, Xop_eqv}, {Op_alu_xo, Xop_slw},
			//{Op_alu_xo, Xop_srw}, {Op_alu_xo, Xop_srawi}, {Op_alu_xo, Xop_sraw},
			//{Op_alu_xo, 1'bz, Xop_neg}, {Op_alu_xo, 1'bz, Xop_subfze},
			//{Op_alu_xo, 1'bz, Xop_subfme}, {Op_alu_xo, 1'bz, Xop_addme},
			//{Op_alu_xo, 1'bz, Xop_addze}, {Op_alu_xo, Xop_extsb},
			//{Op_alu_xo, Xop_extsh}, {Op_alu_xo, Xop_popcb}, 
			//{Op_alu_xo, Xop_prtyw}, {Op_alu_xo, Xop_mfocrf},
			//{Op_alu_xo, Xop_cmp}, {Op_alu_xo, Xop_cmpl},
			//{Op_alu_xo, Xop_mtocrf}, {Op_alu_xo, Xop_mtspr}:
			{Op_bc, 10'bz}, {Op_branch, 10'bz}, {Op_bclr, 10'bz},
			{Op_alu_xo, Xop_wait}: 
				cw_read_gpr_a = 1'b0;

			default:
				cw_read_gpr_a = 1'b1;
		endcase

		unique casez(cop)
			{Op_rlwimi, 10'bz}, {Op_rlwnm, 10'bz}, 
			{Op_alu_xo, 1'bz, Xop_add}, {Op_alu_xo, 1'bz, Xop_addc},
			{Op_alu_xo, 1'bz, Xop_subf}, {Op_alu_xo, 1'bz, Xop_subfc},
			{Op_alu_xo, 1'bz, Xop_adde}, {Op_alu_xo, 1'bz, Xop_subfe},
			{Op_alu_xo, Xop_and}, {Op_alu_xo, Xop_andc}, {Op_alu_xo, Xop_or},
			{Op_alu_xo, Xop_orc}, {Op_alu_xo, Xop_xor}, {Op_alu_xo, Xop_nand},
			{Op_alu_xo, Xop_nor}, {Op_alu_xo, Xop_eqv}, {Op_alu_xo, Xop_slw},
			{Op_alu_xo, Xop_srw}, {Op_alu_xo, Xop_srawi}, {Op_alu_xo, Xop_sraw},
			{Op_alu_xo, Xop_cmp}, {Op_alu_xo, Xop_cmpl},
			{Op_alu_xo, Xop_lwzx}, {Op_alu_xo, Xop_lwzx}, {Op_alu_xo, Xop_lbzx},
			{Op_alu_xo, Xop_stwx}, {Op_alu_xo, Xop_sthx}, {Op_alu_xo, Xop_stbx},
			{Op_alu_xo, Xop_stwux}, {Op_alu_xo, Xop_sthux}, {Op_alu_xo, Xop_stbux}:
				cw_read_gpr_b = 1'b1;

			default:
				cw_read_gpr_b = 1'b0;
		endcase

		unique casez(cop)
			{Op_alu_xo, Xop_stwx}, {Op_alu_xo, Xop_sthx}, {Op_alu_xo, Xop_stbx},
			{Op_alu_xo, Xop_stwux}, {Op_alu_xo, Xop_sthux}, {Op_alu_xo, Xop_stbux},
			{Op_stw, 10'bz}, {Op_stb, 10'bz}, {Op_sth, 10'bz},
			{Op_stwu, 10'bz}, {Op_stbu, 10'bz}, {Op_sthu, 10'bz}:
				cw_read_gpr_c = 1'b1;

			default:
				cw_read_gpr_c = 1'b0;
		endcase
	end
end
*/

always_comb
begin
	// defaults
	cw_read_gpr_a = 1'b0;
	cw_read_gpr_b = 1'b0;
	cw_read_gpr_c = 1'b0;

	if( is_nop == 1'b0 ) begin
		unique case(data.inst.d.opcd)
			// instructions always reading one GPR
			Op_cmpi, Op_cmpli, Op_twi: begin
				cw_read_gpr_a = 1'b1;
			end

			// instructions reading one GPR
			Op_stw, Op_stb, Op_sth,
			Op_stwu, Op_stbu, Op_sthu:
			begin
				cw_read_gpr_a = ~ra_is_zero;
				cw_read_gpr_c = 1'b1;
			end

			// instructions reading RA|0 (i.e. always reading 0 for GPR0)
			// and writing one GPR
			Op_addi, Op_addis, Op_lwz, Op_lhz, Op_lbz:
			begin
				if( !ra_is_zero )
					cw_read_gpr_a = 1'b1;
			end

			// instructions reading and writing one GPR
			Op_addic, Op_addic_rec, Op_subfic:
			begin
				cw_read_gpr_a = 1'b1;
			end

			Op_andi, Op_andis, Op_ori, Op_oris, Op_xori, Op_xoris,
			Op_rlwinm:
			begin
				cw_read_gpr_c = 1'b1;
			end

			// instructions reading two and writing one GPR
			Op_rlwimi, Op_rlwnm:
			begin
				cw_read_gpr_c = 1'b1;
				cw_read_gpr_a = 1'b1;
			end

			Op_alu_xo:
			begin
				unique casez(data.inst.x.xo)
					// instructions reading two and writing one GPR
					{1'bz, Xop_add}, {1'bz, Xop_addc}, {1'bz, Xop_subf},
					{1'bz, Xop_subfc},{1'bz, Xop_adde}, {1'bz, Xop_subfe},
					Xop_tw:
					begin
						cw_read_gpr_a = 1'b1;
						cw_read_gpr_b = 1'b1;
					end

					Xop_and, Xop_andc, Xop_or, Xop_orc, Xop_xor, Xop_nand, 
					Xop_nor, Xop_eqv, 
					Xop_slw, Xop_srw, Xop_srawi, Xop_sraw:
					begin
						cw_read_gpr_c = 1'b1;
						cw_read_gpr_b = 1'b1;
					end
					
					
					// instructions reading one and writing one
					{1'bz, Xop_neg}, {1'bz, Xop_subfze}, {1'bz, Xop_subfme},
					{1'bz, Xop_addme}, {1'bz, Xop_addze}:
					begin
						cw_read_gpr_a = 1'b1;
					end					
					
					Xop_extsb, Xop_extsh,
					Xop_popcb, Xop_prtyw, Xop_mtocrf, Xop_mtspr,
					Xop_mfocrf,  // substitutes only 4bit of the register value
					             // the rest is read in from the old value
					Xop_mtmsr:
					begin
						cw_read_gpr_c = 1'b1;
					end

					// instructions reading two and writing none
					Xop_cmp, Xop_cmpl: begin
						cw_read_gpr_a = 1'b1;
						cw_read_gpr_b = 1'b1;
					end

					// instructions reading RA|0 and RB and writing one
					Xop_lwzx, Xop_lhzx, Xop_lbzx:
					begin
						cw_read_gpr_a = ~ra_is_zero;
						cw_read_gpr_b = 1'b1;
					end

					Xop_stwx, Xop_sthx, Xop_stbx,
					Xop_stwux, Xop_sthux, Xop_stbux:
					begin
						cw_read_gpr_a = ~ra_is_zero;
						cw_read_gpr_b = 1'b1;
						cw_read_gpr_c = 1'b1;
					end

					default: begin end
				endcase
			end

			default: begin end
		endcase
	end
end

always_comb
begin
	logic[15:0] cop;

	// default assignments
	wb_gpr_wr_alu = 1'b0;
	wb_gpr_wr_mem = 1'b0;

	cop = {data.inst.x.opcd, data.inst.x.xo};
	unique casez(cop)
		{Op_addi, 10'bz}, {Op_addis, 10'bz},
		{Op_addic, 10'bz}, {Op_addic_rec, 10'bz}, {Op_subfic, 10'bz},
		{Op_andi, 10'bz}, {Op_andis, 10'bz}, {Op_ori, 10'bz},
		{Op_oris, 10'bz}, {Op_xori, 10'bz}, {Op_xoris, 10'bz},
		{Op_rlwinm, 10'bz},
		{Op_rlwimi, 10'bz}, {Op_rlwnm, 10'bz},
		{Op_alu_xo, 1'bz, Xop_add}, {Op_alu_xo, 1'bz, Xop_addc},
		{Op_alu_xo, 1'bz, Xop_subf}, {Op_alu_xo, 1'bz, Xop_subfc},
		{Op_alu_xo, 1'bz, Xop_adde}, {Op_alu_xo, 1'bz, Xop_subfe},
		{Op_alu_xo, Xop_and}, {Op_alu_xo, Xop_andc}, {Op_alu_xo, Xop_or}, 
		{Op_alu_xo, Xop_orc}, {Op_alu_xo, Xop_xor}, {Op_alu_xo, Xop_nand}, 
		{Op_alu_xo, Xop_nor}, {Op_alu_xo, Xop_eqv}, {Op_alu_xo, Xop_slw}, 
		{Op_alu_xo, Xop_srw}, {Op_alu_xo, Xop_srawi}, {Op_alu_xo, Xop_sraw},
		{Op_alu_xo, 1'bz, Xop_neg}, {Op_alu_xo, 1'bz, Xop_subfze},
		{Op_alu_xo, 1'bz, Xop_subfme}, {Op_alu_xo, 1'bz, Xop_addme},
		{Op_alu_xo, 1'bz, Xop_addze},
		{Op_alu_xo, Xop_extsb}, {Op_alu_xo, Xop_extsh}, {Op_alu_xo, Xop_popcb},
		{Op_alu_xo, Xop_prtyw},
		{Op_alu_xo, Xop_mfocrf}, // only needed for dependency tracking

			// actually for mfspr this control signal is ignored in write_back
			// it is set nevertheless to track the write access
			// for data hazards
		{Op_alu_xo, Xop_mfspr},
		{Op_alu_xo, Xop_mfmsr}:
		begin
			wb_gpr_wr_alu = ~is_nop;
		end

		{Op_stwu, 10'bz}, {Op_sthu, 10'bz}, {Op_stbu, 10'bz},
		{Op_alu_xo, Xop_stwux}, {Op_alu_xo, Xop_sthux}, {Op_alu_xo, Xop_stbux}:
		begin
			wb_gpr_wr_alu = ~is_nop && (ls_ctr == 0);
		end


		{Op_lwz, 10'bz}, {Op_lhz, 10'bz}, {Op_lbz, 10'bz},
		{Op_alu_xo, Xop_lwzx}, {Op_alu_xo, Xop_lhzx}, {Op_alu_xo, Xop_lbzx}:
		begin
			wb_gpr_wr_mem = 1'b1;
		end

		default: begin end
	endcase
end
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// select the destination GPR for this instruction
always_comb
begin
	unique case(data.inst.xo.opcd)
		Op_ori, Op_oris, Op_andi, Op_andis, Op_xori, Op_xoris,
		Op_rlwimi, Op_rlwinm, Op_rlwnm,
		Op_stwu, Op_sthu, Op_stbu:
		begin
			wb_gpr_dest_alu = data.inst.d.ra;
		end

		Op_alu_xo: begin
			unique case(data.inst.x.xo)
				Xop_and, Xop_andc, Xop_or, Xop_orc, Xop_xor, 
				Xop_nand, Xop_nor, Xop_eqv, Xop_extsb, Xop_extsh,
				Xop_slw, Xop_srw, Xop_srawi, Xop_sraw,
				Xop_popcb, Xop_prtyw,
				Xop_stwux, Xop_sthux, Xop_stbux:
					wb_gpr_dest_alu = data.inst.d.ra;
				default:
					wb_gpr_dest_alu = data.inst.d.rt;
			endcase
		end

		default:  wb_gpr_dest_alu = data.inst.d.rt;
	endcase
end

assign wb_gpr_dest_mem = data.inst.d.rt;
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Detect reads from and writes to CTR
always_comb
begin
	logic[15:0] cop;

	cw_read_ctr = 1'b0;
	cw_write_ctr = 1'b0;

	cop = { data.inst.xl.opcd, data.inst.xl.xo };
	casez(cop)
		{Op_bc, 10'bzzzzzzzzzz}:
			if( data.inst.b.bo[2] == 1'b0 ) begin
				cw_read_ctr = 1'b1;
				cw_write_ctr = 1'b1;
			end

		{Op_bclr, Xxop_bclr}:
			if( data.inst.b.bo[2] == 1'b0 )
			begin
				cw_read_ctr = 1'b1;
				cw_write_ctr = 1'b1;
			end

		{Op_bclr, Xxop_bcctr}:
			cw_read_ctr = 1'b1;

		{Op_alu_xo, Xop_mtspr}:
			if( data.inst.xfx.spr == Spr_ctr )
				cw_write_ctr = 1'b1;

		{Op_alu_xo, Xop_mfspr}:
			if( data.inst.xfx.spr == Spr_ctr )
				cw_read_ctr = 1'b1;
	endcase
end
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Detect reads from LNK
always_comb
begin
	if( (data.inst.xl.opcd == Op_bclr && data.inst.xl.xo == Xxop_bclr)
		|| (data.inst.xfx.opcd == Op_alu_xo && data.inst.xfx.xo == Xop_mfspr
		    && data.inst.xfx.spr == Spr_lnk) )
		cw_read_lnk = 1'b1;
	else
		cw_read_lnk = 1'b0;
end
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Detect writes to LNK
always_comb
begin
	logic[15:0] cop;

	cw_write_lnk = 1'b0;

	cop = {data.inst.xl.opcd, data.inst.xl.xo};
	casez(cop)
		{Op_branch, 10'bzzzzzzzzzz},
		{Op_bc,     10'bzzzzzzzzzz},
		{Op_bclr,   Xxop_bclr},
		{Op_bclr,   Xxop_bcctr}:
		begin
			cw_write_lnk = data.inst.xl.lk;
		end

		{Op_alu_xo, Xop_mtspr}:
			if( data.inst.xfx.spr == Spr_lnk )
				cw_write_lnk = 1'b1;

		{Op_bclr, Xxop_rfi}, {Op_bclr, Xxop_rfci},
		{Op_bclr, Xxop_rfmci}:
			cw_write_lnk = 1'b0;
	endcase
end
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Select ALU operation
//---------------------------------------------------------------------------
always_comb
begin
	unique case(data.inst.d.opcd)
		Op_subfic:
			alu_op = Alu_sub;

		Op_andi, Op_andis:
			alu_op = Alu_and;

		Op_ori, Op_oris:
			alu_op = Alu_or;

		Op_xori, Op_xoris:
			alu_op = Alu_xor;

		Op_rlwimi, Op_rlwinm, Op_rlwnm:
			alu_op = Alu_rotl;

		Op_cmpi:
			alu_op = Alu_cmp;

		Op_cmpli:
			alu_op = Alu_cmpl;

		Op_alu_xo: begin
			unique casez(data.inst.x.xo)
				{1'bz, Xop_add}, {1'bz, Xop_addc}, {1'bz, Xop_addme},
				{1'bz, Xop_addze}, {1'bz, Xop_adde}:
					alu_op = Alu_add;

				{1'bz, Xop_subf}, {1'bz, Xop_subfc}, {1'bz, Xop_subfme},
				{1'bz, Xop_subfze}, {1'bz, Xop_subfe}:
					alu_op = Alu_sub;

				Xop_cmp:            alu_op = Alu_cmp;
				Xop_cmpl:           alu_op = Alu_cmpl;
				{1'bz, Xop_neg}:    alu_op = Alu_neg;
				Xop_and:            alu_op = Alu_and;
				Xop_andc:           alu_op = Alu_andc;
				Xop_or:             alu_op = Alu_or;
				Xop_orc:            alu_op = Alu_orc;
				Xop_xor:            alu_op = Alu_xor;
				Xop_nand:           alu_op = Alu_nand;
				Xop_nor:            alu_op = Alu_nor;
				Xop_eqv:            alu_op = Alu_eqv;
				Xop_extsb:          alu_op = Alu_esb;
				Xop_extsh:          alu_op = Alu_esh;
				
				Xop_slw, Xop_srw, Xop_srawi, Xop_sraw:
				                    alu_op = Alu_rotl;

				Xop_popcb:          alu_op = Alu_popcnt;
				Xop_prtyw:          alu_op = Alu_prty;
				default:            alu_op = Alu_add;
			endcase
		end

		default:
			alu_op = Alu_add;
	endcase
end

//---------------------------------------------------------------------------
// control CR logic control signals
//---------------------------------------------------------------------------
assign alu_crl_ba = data.inst.xl.ba;
assign alu_crl_bb = data.inst.xl.bb;
assign alu_crl_bt = data.inst.xl.bt;

always_comb
begin
	// default assignment
	cr_op = Cr_and;

	if( data.inst.xl.opcd == Op_bclr ) begin
		unique case(data.inst.xl.xo)
			Xxop_crand:         cr_op = Cr_and;
			Xxop_crnand:        cr_op = Cr_nand;
			Xxop_cror:          cr_op = Cr_or;
			Xxop_crnor:         cr_op = Cr_nor;
			Xxop_crxor:         cr_op = Cr_xor;
			Xxop_creqv:         cr_op = Cr_eqv;
			Xxop_crandc:        cr_op = Cr_andc;
			Xxop_crorc:         cr_op = Cr_orc;
			default:            cr_op = Cr_and;
		endcase
	end
end

//---------------------------------------------------------------------------
// Control fixedpoint write back multiplexer
//---------------------------------------------------------------------------
always_comb
begin
	// default assignment
	fxdp_sel = Fu_alu;

	case(data.inst.d.opcd)  // TODO mul/div instructions
		Op_rlwimi, Op_rlwinm, Op_rlwnm:
			fxdp_sel = Fu_rotm;

		Op_alu_xo: begin
			case(data.inst.x.xo)
				Xop_slw, Xop_srw, Xop_srawi, Xop_sraw:
					fxdp_sel = Fu_rotm;

				Xop_mfspr, Xop_mfocrf, Xop_mtocrf, Xop_mfmsr, Xop_mtmsr:
					fxdp_sel = Fu_spreu;
			endcase
		end

		Op_bclr:
			fxdp_sel = Fu_spreu;
	endcase
end

//---------------------------------------------------------------------------
// Generate branch control signals
//---------------------------------------------------------------------------
always_comb
begin
	br_crbi = data.inst.b.bi;
	br_cond = data.inst.b.bo[3];
	br_mask_cond = data.inst.b.bo[4];
	br_ctr_eq = data.inst.b.bo[1];
	br_mask_ctr = data.inst.b.bo[2];
	br_save_lnk = data.inst.i.lk;

	// default assignments
	br_jump = 1'b0;
	br_dec_ctr = 1'b0;

	unique case(data.inst.d.opcd)
		Op_branch: begin
			br_jump = 1'b1;
			br_dec_ctr = 1'b0;
		end
		
		Op_bc: begin
			br_jump = 1'b0;
			br_dec_ctr = ~data.inst.b.bo[2];
		end

		Op_bclr: begin
			case(data.inst.xl.xo)
				Xxop_bclr, Xxop_bcctr: begin
					br_jump = 1'b0;
					br_dec_ctr = ~data.inst.b.bo[2];
				end

				Xxop_rfi, Xxop_rfci, Xxop_rfmci: begin
					br_jump = 1'b1;
					br_save_lnk = 1'b0;
				end
			endcase
		end

		default: begin
			br_jump = 1'b0;
			br_dec_ctr = 1'b0;
		end
	endcase
end

//---------------------------------------------------------------------------
// Generate trap control signals
//---------------------------------------------------------------------------
always_comb
	trap_to = data.inst.x.rt;

//---------------------------------------------------------------------------
// Control memory write
//---------------------------------------------------------------------------
always_comb
begin
	logic[15:0] cop;

	cop = {data.inst.x.opcd, data.inst.x.xo};
	unique casez(cop)
		{Op_stw, 10'bzzzzzzzzzz}, {Op_sth, 10'bzzzzzzzzzz}, {Op_stb, 10'bzzzzzzzzzz},
		{Op_stwu, 10'bzzzzzzzzzz}, {Op_sthu, 10'bzzzzzzzzzz}, {Op_stbu, 10'bzzzzzzzzzz},
		{Op_alu_xo, Xop_stwx}, {Op_alu_xo, Xop_sthx},
		{Op_alu_xo, Xop_stbx},
		{Op_alu_xo, Xop_stwux}, {Op_alu_xo, Xop_sthux},
		{Op_alu_xo, Xop_stbux}:
			ls_we = 1'b1;

		default:
			ls_we = 1'b0;
	endcase
end

always_comb
begin : mem_write_mode
	logic[15:0] cop;

	cop = {data.inst.x.opcd, data.inst.x.xo};

	unique casez(cop)
		{Op_stb, 10'bz}, {Op_lbz, 10'bz},
		{Op_stbu, 10'bz},
		{Op_alu_xo, Xop_lbzx}, {Op_alu_xo, Xop_stbx},
		{Op_alu_xo, Xop_stbux}:
			ls_mode = Load_byte;

		{Op_sth, 10'bz}, {Op_lhz, 10'bz},
		{Op_sthu, 10'bz},
		{Op_alu_xo, Xop_lhzx}, {Op_alu_xo, Xop_sthx},
		{Op_alu_xo, Xop_sthux}:
			ls_mode = Load_halfword;

		default:
			ls_mode = Load_word;
	endcase
end : mem_write_mode

//---------------------------------------------------------------------------
// Select GPR writeback input
//---------------------------------------------------------------------------
// always_comb
// begin
// 	logic[15:0] cop;
// 
// 	cop = {data.inst.d.opcd, data.inst.x.xo};
// 	unique casez(cop)
// 		{Op_lwz, 10'bz}, {Op_stw, 10'bz}, {Op_lhz, 10'bz},
// 		{Op_sth, 10'bz}, {Op_lbz, 10'bz}, {Op_stb, 10'bz},
// 		{Op_alu_xo, Xop_lwzx}, {Op_alu_xo, Xop_lhzx}, {Op_alu_xo, Xop_lbzx}:
// 			wb_use_alu = 1'b0;
// 
// 		default:
// 			wb_use_alu = 1'b1;
// 	endcase
// end

//---------------------------------------------------------------------------
// Control recording to condition register
//---------------------------------------------------------------------------
always_comb
begin
	unique case(data.inst.d.opcd)
		Op_andi, Op_andis, Op_addic_rec:
			wb_record_cr = 8'h01;

		Op_cmpi, Op_cmpli: begin
			wb_record_cr = 8'h00;
			wb_record_cr[data.inst.d.rt[4:2]] = 1'b1;
		end

		Op_rlwimi, Op_rlwinm, Op_rlwnm:
			wb_record_cr = {7'h00, data.inst.m.rc};

		Op_alu_xo: begin
			unique case(data.inst.x.xo)
				Xop_cmp, Xop_cmpl: begin
					wb_record_cr = 8'h00;
					wb_record_cr[data.inst.x.rt[4:2]] = 1'b1;
				end

				Xop_popcb, Xop_prtyw, Xop_mfocrf, Xop_wait,
				Xop_mtmsr, Xop_mfmsr, Xop_tw:
					wb_record_cr = 8'h00;

				Xop_mtocrf: begin
					for(int i=0; i<8; i++)
						wb_record_cr[i] = data.inst.xfx.spr[8-i];
				end

				Xop_lwzx, Xop_lhzx, Xop_lbzx,
				Xop_stwx, Xop_sthx, Xop_stbx,
				Xop_stwux, Xop_sthux, Xop_stbux:
					wb_record_cr = 8'b0;

				default:
					wb_record_cr = {7'h00, data.inst.xo.rc};
			endcase
		end

		Op_bclr: begin
			wb_record_cr = 8'h00;

			unique case(data.inst.xl.xo)
				Xxop_crand, Xxop_crnand, Xxop_cror, Xxop_cror, Xxop_crnor,
				Xxop_crxor, Xxop_creqv, Xxop_crorc, Xxop_crandc, Xxop_mcrf:
					wb_record_cr[data.inst.xl.bt[4:2]] = 1'b1;

				default:
					wb_record_cr = 8'h00;
			endcase
		end

		default:
			wb_record_cr = 8'h00;
	endcase

	cw_write_cr = wb_record_cr;
end


always_comb
begin : set_wr_cr
	wb_wr_cr = 1'b0;

	if( data.inst.xl.opcd == Op_bclr )
		unique case(data.inst.xl.xo)
			Xxop_crand, Xxop_crnand, Xxop_cror, Xxop_cror, Xxop_crnor,
			Xxop_crxor, Xxop_creqv, Xxop_crorc, Xxop_crandc, Xxop_mcrf:
				wb_wr_cr = 1'b1;

			default:
				wb_wr_cr = 1'b0;
		endcase
	else if( (data.inst.xfx.opcd == Op_alu_xo) && (data.inst.xfx.xo == Xop_mtocrf) )
		wb_wr_cr = 1'b1;
	else
		wb_wr_cr = 1'b0;
end : set_wr_cr

//---------------------------------------------------------------------------
// control recording to XER register
//---------------------------------------------------------------------------
always_comb
begin : gen_record_ca
// does not work with modelsim 6.5b:
/*	unique case({data.inst.xo.opcd, data.inst.xo.xo})
		{Op_alu_xo, Xop_addc}:   wb_record_ca = 1'b1;
		{Op_alu_xo, Xop_subfc}:  wb_record_ca = 1'b1;
		default:                 wb_record_ca = 1'b0;
	endcase */

// but with temporary variable works...
	logic[15:0] cop;

	cop = {data.inst.xo.opcd, data.inst.x.xo};
	unique casez(cop)
		{Op_subfic, 10'bz}:              wb_record_ca = 1'b1;
		{Op_addic, 10'bz}:               wb_record_ca = 1'b1;
		{Op_addic_rec, 10'bz}:           wb_record_ca = 1'b1;
		{Op_alu_xo, 1'bz, Xop_addc}:     wb_record_ca = 1'b1;
		{Op_alu_xo, 1'bz, Xop_subfc}:    wb_record_ca = 1'b1;
		{Op_alu_xo, 1'bz, Xop_adde}:     wb_record_ca = 1'b1;
		{Op_alu_xo, 1'bz, Xop_addme}:    wb_record_ca = 1'b1;
		{Op_alu_xo, 1'bz, Xop_addze}:    wb_record_ca = 1'b1;
		{Op_alu_xo, 1'bz, Xop_subfe}:    wb_record_ca = 1'b1;
		{Op_alu_xo, 1'bz, Xop_subfze}:   wb_record_ca = 1'b1;
		{Op_alu_xo, 1'bz, Xop_subfme}:   wb_record_ca = 1'b1;

		{Op_alu_xo, Xop_srawi},
		{Op_alu_xo, Xop_sraw}:           wb_record_ca = 1'b1;
		default:                         wb_record_ca = 1'b0;
	endcase
end : gen_record_ca

always_comb
begin : gen_record_ov
	unique case(data.inst.d.opcd)
		Op_alu_xo: begin
			unique case(data.inst.x.xo)
				Xop_and, Xop_andc, Xop_or, Xop_orc, Xop_xor, 
				Xop_nand, Xop_nor, Xop_xor, Xop_eqv, Xop_extsb, Xop_extsh,
				Xop_slw, Xop_srw, Xop_srawi, Xop_sraw,
				Xop_lwzx, Xop_lhzx, Xop_lbzx,
				Xop_stwx, Xop_sthx, Xop_stbx,
				Xop_stwux, Xop_sthux, Xop_stbx, Xop_wait:
				          wb_record_ov = 1'b0;
				default:  wb_record_ov = data.inst.xo.oe;
			endcase
		end

		default:       wb_record_ov = 1'b0;
	endcase
end : gen_record_ov

// monitor writes from mtspr instructions
always_comb
	if( data.inst.d.opcd == Op_alu_xo 
			&& data.inst.xfx.xo == Xop_mtspr
			&& data.inst.xfx.spr == Spr_xer )
		write_xer = 1'b1;
	else
		write_xer = 1'b0;


always_comb cw_write_xer = wb_record_ca | wb_record_ov | write_xer;

always_comb
begin : gen_xer_read
	logic[14:0] cop;
	cop = {data.inst.xo.opcd, data.inst.xo.xo};

	cw_read_xer = 1'b0;

	if( data.inst.xo.opcd == Op_alu_xo && data.inst.xfx.xo == Xop_mfspr
		&& data.inst.xfx.spr == Spr_xer )
		cw_read_xer = 1'b1;
	else if( data.inst.xo.opcd == Op_alu_xo )
		case(data.inst.xo.xo)
			Xop_addme, Xop_addze, Xop_subfe, Xop_subfme,
			Xop_subfze, Xop_adde:
				cw_read_xer = 1'b1;

			default:
				cw_read_xer = data.inst.xo.rc;
		endcase
	else 
		case(data.inst.xo.opcd)
			Op_rlwimi, Op_rlwinm, Op_rlwnm, Op_cmpli, Op_cmpi:
				cw_read_xer = data.inst.xo.rc;  // same as data.inst.m.rc

			default:
				cw_read_xer = 1'b0;
		endcase

	//priority casez(cop)
		//{Op_alu_xo, Xop_addme},
		//{Op_alu_xo, Xop_addze},
		//{Op_alu_xo, Xop_subfe},
		//{Op_alu_xo, Xop_subfme},
		//{Op_alu_xo, Xop_subfze},
		//{Op_alu_xo, Xop_adde}:       cw_read_xer = 1'b1;

		//// if the instructions records to condition register it has to read the
		//// SO bit from XER.
		//{Op_alu_xo, 9'bzzzzzzzzz}:   cw_read_xer = data.inst.xo.rc;
		//{Op_rlwimi, 9'bzzzzzzzzz},
		//{Op_rlwinm, 9'bzzzzzzzzz},
		//{Op_rlwnm,  9'bzzzzzzzzz},
		//{Op_cmpli,  9'bzzzzzzzzz},
		//{Op_cmpi,   9'bzzzzzzzzz}:   cw_read_xer = data.inst.m.rc;
	//endcase
end : gen_xer_read
//---------------------------------------------------------------------------
// Forward next PC to write_back
//---------------------------------------------------------------------------
assign wb_lnk = data.npc;

//---------------------------------------------------------------------------
// Detect reads from condition register
//---------------------------------------------------------------------------
function automatic logic[7:0] cr_idx_decode(input logic[2:0] idx);
	logic[7:0] rv;
	
	unique case(idx)
		3'd0:    rv = 8'b0000_0001;
		3'd1:    rv = 8'b0000_0010;
		3'd2:    rv = 8'b0000_0100;
		3'd3:    rv = 8'b0000_1000;
		3'd4:    rv = 8'b0001_0000;
		3'd5:    rv = 8'b0010_0000;
		3'd6:    rv = 8'b0100_0000;
		3'd7:    rv = 8'b1000_0000;
		default: rv = 8'bxxxx_xxxx;
	endcase

	return rv;
endfunction;


always_comb
begin
	// defaults
	cw_read_cr_0 = '0;
	cw_read_cr_1 = '0;
	cw_read_cr_2 = '0;

	unique case(data.inst.d.opcd)
		Op_bc: begin
			// conditional branch reads CR, when the mask bit is not set
			if( data.inst.b.bo[4] == 1'b0 ) 
				cw_read_cr_0 = cr_idx_decode(data.inst.b.bi[4:2]);
		end

		Op_bclr: begin
			unique case(data.inst.xl.xo)
				Xxop_bclr, Xxop_bcctr: begin
					if( data.inst.b.bo[4] == 1'b0 ) 
						cw_read_cr_0 = cr_idx_decode(data.inst.b.bi[4:2]);
				end

				Xxop_crand, Xxop_crnand, Xxop_cror, Xxop_cror, Xxop_crnor,
				Xxop_crxor, Xxop_creqv, Xxop_crorc, Xxop_crandc:
				begin
					cw_read_cr_0 = cr_idx_decode(data.inst.xl.ba[4:2]);
					cw_read_cr_1 = cr_idx_decode(data.inst.xl.bb[4:2]);

					/* these instructions work on individual bits, so also the
					* target field has to be read, because the other bits are
					* taken unchanged from the field. */
					cw_read_cr_2 = cr_idx_decode(data.inst.xl.bt[4:2]);
				end

				Xxop_mcrf: begin
					cw_read_cr_0 = cr_idx_decode(data.inst.xl.ba[4:2]);
				end

				default:
					cw_read_cr_0 = '0;
			endcase
		end

		Op_alu_xo: begin
			if( data.inst.xfx.xo == Xop_mfocrf ) begin
				for(int i=0; i<8; i++)
					cw_read_cr_0[i] = data.inst.xfx.spr[8-i];
			end
		end

		default: begin
		end
	endcase
end

//---------------------------------------------------------------------------
// Control signals for register-register transfers
//---------------------------------------------------------------------------
assign 
	wb_spr_sel = data.inst.xfx.spr,
	cw_spr_dest = Spr_reduced'(data.inst.xfx.spr);

//always_comb
// This seems to be another ModelSim bug:
// Using always_comb the process is not always triggered at changes of spr
// Perhaps because of the indexing?
always @(data.inst.d.opcd, data.inst.xl.xo, data.inst.xl.ba, data.inst.xfx.spr)
begin
	if( data.inst.d.opcd == Op_bclr && data.inst.xl.xo == Xxop_mcrf ) begin
		logic[2:0] ba;
		ba = data.inst.xl.ba[4:2];
		unique case(ba)
			3'b000:   wb_src_cr = 8'b10000000;
			3'b001:   wb_src_cr = 8'b01000000;
			3'b010:   wb_src_cr = 8'b00100000;
			3'b011:   wb_src_cr = 8'b00010000;
			3'b100:   wb_src_cr = 8'b00001000;
			3'b101:   wb_src_cr = 8'b00000100;
			3'b110:   wb_src_cr = 8'b00000010;
			3'b111:   wb_src_cr = 8'b00000001;
			//default:  wb_src_cr = 8'b10000000;
			default:  wb_src_cr = 8'bxxxxxxxx;
		endcase
	end else begin
		wb_src_cr[7:0] = data.inst.xfx.spr[8:1];
	end
end

always_comb
begin
	wb_reg_mv = Rmv_none;

	if( data.inst.d.opcd == Op_alu_xo ) begin
		unique case(data.inst.xfx.xo)
			Xop_mtocrf:   wb_reg_mv = Rmv_gtc;  
			Xop_mfocrf:   wb_reg_mv = Rmv_ctg;  
			Xop_mtspr:    wb_reg_mv = Rmv_gts;  
			Xop_mfspr:    wb_reg_mv = Rmv_stg;  
			Xop_mtmsr:    wb_reg_mv = Rmv_gtm;
			Xop_mfmsr:    wb_reg_mv = Rmv_mtg;
			default:      wb_reg_mv = Rmv_none; 
		endcase
	end else if( data.inst.d.opcd == Op_bclr ) begin
		if( data.inst.xl.xo == Xxop_mcrf ) 
			wb_reg_mv = Rmv_ctc;
	end
end

always_comb
	if( data.inst.d.opcd == Op_alu_xo && data.inst.xfx.xo == Xop_mtspr ) begin
		cw_write_spr = 1'b1;
		wb_spr_we = 1'b1;
	end else begin
		cw_write_spr = 1'b0;
		wb_spr_we = 1'b0;
	end

always_comb
begin
	// default assignment
	cw_read_spr = 1'b0;
	cw_read_spr2 = 1'b0;

	if( data.inst.xfx.opcd == Op_alu_xo && data.inst.xfx.xo == Xop_mfspr )
	begin
		cw_read_spr = 1'b1;
	end else if( data.inst.xl.opcd == Op_bclr && (data.inst.xl.xo == Xxop_rfi 
			|| data.inst.xl.xo == Xxop_rfci
			|| data.inst.xl.xo == Xxop_rfmci) )
	begin
		cw_read_spr = 1'b1;
		cw_read_spr2 = 1'b1;
	end
end

always_comb 
	if( data.inst.xl.opcd == Op_bclr )
		unique case(data.inst.xl.xo)
			Xxop_rfi: begin
				cw_spr_src = Spr_srr0;
				cw_spr_src2 = Spr_srr1;
			end

			Xxop_rfci: begin
				cw_spr_src = Spr_csrr0;
				cw_spr_src2 = Spr_csrr1;
			end

			Xxop_rfmci: begin
				cw_spr_src = Spr_mcsrr0;
				cw_spr_src2 = Spr_mcsrr1;
			end

			default: begin
				cw_spr_src = Spr_srr0;
				cw_spr_src2 = Spr_srr1;
			end
		endcase
	else begin
		cw_spr_src = Spr_reduced'(data.inst.xfx.spr);
		cw_spr_src2 = Spr_srr1;
	end

always_comb
	if( data.inst.x.opcd == Op_alu_xo && data.inst.x.xo == Xop_mtmsr )
		wb_msr_we = 1'b1;
	else
		wb_msr_we = 1'b0;

//---------------------------------------------------------------------------
// Interrupt restore signals
//---------------------------------------------------------------------------
always_comb
begin
	// default asssignment
	int_rest_base = 1'b0;
	int_rest_crit = 1'b0;
	int_rest_mcheck = 1'b0;

	if( data.inst.xl.opcd == Op_bclr )
		case(data.inst.xl.xo)
			Xxop_rfi:    int_rest_base = 1'b1;
			Xxop_rfci:   int_rest_crit = 1'b1;
			Xxop_rfmci:  int_rest_mcheck = 1'b1;
		endcase
end

//---------------------------------------------------------------------------
// Context synchronization control
//---------------------------------------------------------------------------

always_comb begin
  // default assignment
  int_block_external = 1'b0;
  start_sync = 1'b0;

  if( {data.inst.x.opcd, data.inst.x.xo} == {Op_alu_xo, Xop_mtmsr} ) begin
    int_block_external = 1'b1;
    start_sync = 1'b1;
  end
end


always_ff @(posedge clk or posedge reset)
  if( reset )
    sync_sreg <= '0;
  else
    sync_sreg <= { (start_sync & ~(| sync_sreg)), sync_sreg[0:1] };

//---------------------------------------------------------------------------
// Produce output set of control signals
//---------------------------------------------------------------------------
always_comb begin : write_control_word
	if( active ) begin
		// default assignment
		cw = {$bits(cw){1'b0}};

		cw.if_hold = if_hold;
		cw.if_wait = if_wait;
		cw.read_xer = cw_read_xer;
		cw.write_xer = cw_write_xer;
		cw.read_cr_0 = cw_read_cr_0;
		cw.read_cr_1 = cw_read_cr_1;
		cw.read_cr_2 = cw_read_cr_2;
		cw.write_cr = cw_write_cr;
		cw.read_ctr = cw_read_ctr;
		cw.write_ctr = cw_write_ctr;
		cw.read_lnk = cw_read_lnk;
		cw.write_lnk = cw_write_lnk;
		cw.gpr_a = cw_gpr_a;
		cw.gpr_b = cw_gpr_b;
		cw.gpr_c = cw_gpr_c;
		cw.read_gpr_a = cw_read_gpr_a;
		cw.read_gpr_b = cw_read_gpr_b;
		cw.read_gpr_c = cw_read_gpr_c;
		cw.gpr_from_alu = wb_gpr_dest_alu;
		cw.gpr_from_mem = wb_gpr_dest_mem;
		cw.write_gpr_from_alu = wb_gpr_wr_alu;
		cw.write_gpr_from_mem = wb_gpr_wr_mem;
		cw.read_spr = cw_read_spr;
		cw.read_spr2 = cw_read_spr2;
		cw.write_spr = cw_write_spr;
		cw.spr_src = cw_spr_src;
		cw.spr_src2 = cw_spr_src2;
		cw.spr_dest = cw_spr_dest;

		if( !is_nop ) begin
			// ALU signals
			cw.alu_en = alu_en;
			cw.alu_op = alu_op;
			cw.alu_crl_ba = alu_crl_ba;
			cw.alu_crl_bb = alu_crl_bb;
			cw.alu_crl_bt = alu_crl_bt;

			cw.cr_op = cr_op;

			cw.fxdp_sel = fxdp_sel;

			// branch signals
			cw.branch_en = branch_en;
			cw.br_jump = br_jump;
			cw.br_crbi = br_crbi;
			cw.br_cond = br_cond;
			cw.br_mask_cond = br_mask_cond;
			cw.br_ctr_eq = br_ctr_eq;
			cw.br_mask_ctr = br_mask_ctr;
			cw.br_dec_ctr = br_dec_ctr;
			cw.br_save_lnk = br_save_lnk;

			cw.trap_en = trap_en;
			cw.trap_to = trap_to;

			// load/store signals
			cw.ls_en = ls_en;
			cw.ls_we = ls_we;
			cw.ls_mode = ls_mode;

			// writeback signals
			cw.wb_wr_cr = wb_wr_cr;
			cw.wb_record_cr = wb_record_cr;
			cw.wb_record_ca = wb_record_ca;
			cw.wb_record_ov = wb_record_ov;
			cw.wb_src_cr = wb_src_cr;
			cw.wb_reg_mv = wb_reg_mv;
			cw.wb_spr_we = wb_spr_we;
			cw.wb_spr_sel = wb_spr_sel;
			cw.wb_msr_we = wb_msr_we;
			cw.wb_sleep = wb_sleep;

			// interrupt scheduler signals
			cw.int_rest_base = int_rest_base;
			cw.int_rest_crit = int_rest_crit;
			cw.int_rest_mcheck = int_rest_mcheck;
      cw.int_block_external = int_block_external;
		end else begin
			// ALU signals
			cw.alu_en = '0;
			cw.alu_op = Alu_andc;  // has value 0
			cw.alu_crl_ba = '0;
			cw.alu_crl_bb = '0;
			cw.alu_crl_bt = '0;

			cw.cr_op = Cr_and;

			cw.fxdp_sel = Fu_none;

			// branch signals
			cw.branch_en = '0;
			cw.br_jump = '0;
			cw.br_crbi = '0;
			cw.br_cond = '0;
			cw.br_mask_cond = '0;
			cw.br_ctr_eq = '0;
			cw.br_mask_ctr = '0;
			cw.br_dec_ctr = '0;
			cw.br_save_lnk = '0;

			cw.trap_en = 1'b0;
			cw.trap_to = '0;

			// load/store signals
			cw.ls_en = 1'b0;
			cw.ls_we = '0;
			cw.ls_mode = Load_null;

			// writeback signals
			cw.wb_wr_cr = '0;
			cw.wb_record_cr = '0;
			cw.wb_record_ca = '0;
			cw.wb_record_ov = '0;
			cw.wb_src_cr = '0;
			cw.wb_reg_mv = Rmv_none;
			cw.wb_spr_we = 1'b0;
			cw.wb_spr_sel = '0;
			cw.wb_msr_we = 1'b0;
			cw.wb_sleep = 1'b0;

			cw.int_rest_base = 1'b0;
			cw.int_rest_crit = 1'b0;
			cw.int_rest_mcheck = 1'b0;
      cw.int_block_external = 1'b0;

		end
	end else begin
		//{>> {cw}} = {$bits(cw){1'b0}};
		cw = {$bits(cw){1'b0}};
	end
end


//---------------------------------------------------------------------------
// Embedded assertions
//---------------------------------------------------------------------------
// synopsys translate_off

sequence load_with_update;
 	data.inst.d.opcd == Op_lwzu
 	|| data.inst.d.opcd == Op_lhzu
 	|| data.inst.d.opcd == Op_lbzu
	|| (data.inst.d.opcd == Op_alu_xo && data.inst.x.xo == Xop_lwzux)
	|| (data.inst.d.opcd == Op_alu_xo && data.inst.x.xo == Xop_lhzux)
	|| (data.inst.d.opcd == Op_alu_xo && data.inst.x.xo == Xop_lbzux);
endsequence

sequence store_with_update;
	data.inst.d.opcd == Op_stwu
	|| data.inst.d.opcd == Op_sthu
 	|| data.inst.d.opcd == Op_stbu
	|| (data.inst.d.opcd == Op_alu_xo && data.inst.x.xo == Xop_stwux)
	|| (data.inst.d.opcd == Op_alu_xo && data.inst.x.xo == Xop_sthux)
	|| (data.inst.d.opcd == Op_alu_xo && data.inst.x.xo == Xop_stbux);
endsequence

//
// Check for illegal instruction forms
//

illegal_load_store_with_update: assert property (
	@(posedge clk) disable iff (reset)
	((load_with_update or store_with_update)
	 |-> (data.inst.d.ra != '0))
);

illegal_load_store_with_update_2: assert property (
	@(posedge clk) disable iff (reset)
	(load_with_update
	 |-> (data.inst.d.ra != data.inst.d.rt))
);

// synopsys translate_on

endmodule
