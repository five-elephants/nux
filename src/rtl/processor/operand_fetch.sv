/* _use_m4_ macros: include(ops.m4) */

// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.




module Operand_fetch
  ( input logic clk, reset,
    Register_file_if.read register_file,
    Timer_if.op_fetch timer,
    input Frontend::Issue_slot inst,
    input Frontend::Predecoded predec,
    Operand_if.write opbus);

import Pu_types::*;
import Pu_inst::*;
import Frontend::Issue_slot;
import Frontend::Predecoded;
import Frontend::Issue_slot_bits;
import Frontend::Predecoded_bits;
import Frontend::predecoded_zeros;
import Backend::*;

//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

Operands ops;
Operands next_ops;
Inst ir;
Word immediate;
logic ra_is_zero;
Predecoded predec_d;
Issue_slot inst_d;
Word sprin;


assign ir = inst_d.ir;
assign 
  register_file.gpr_sel_a = predec.ra,
  register_file.gpr_sel_b = predec.rb,
  register_file.gpr_sel_c = predec.rt;


assign next_ops.cr = register_file.cr;

assign opbus.opbus_0 = ops;

always_comb begin
  Xer tmp;

  tmp = Xer'(register_file.xer[31:29]);
  next_ops.so = tmp.so;
end


always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    //{>> {predec_d}} <= Predecoded_bits'('0);  // crashes synplify
    predec_d <= predecoded_zeros();
    inst_d.valid <= 1'b0;
  end else begin
    predec_d <= predec;
    inst_d <= inst;
  end

//---------------------------------------------------------------------------
// detect RA == 0 for instructions using RA|0
//---------------------------------------------------------------------------
always_comb 
  if( ir.d.ra == 0 ) 
    ra_is_zero = 1'b1;
  else
    ra_is_zero = 1'b0;

//---------------------------------------------------------------------------
// Multiplexing
//---------------------------------------------------------------------------

always_comb begin 
  OPCMP(ir)
    LOAD_IMMEDIATE_OPS, STORE_IMMEDIATE_OPS, LOAD_INDEXED_OPS, STORE_INDEXED_OPS,
    OP(Op_addi), OP(Op_addis), OP(Op_lmw), OP(Op_stmw), DEV_CTRL_OPS,
    OPFXV(Xop_fxvlax), OPFXV(Xop_fxvstax), OPFXV(Xop_fxvinx),
    OPFXV(Xop_fxvoutx):
      if( ra_is_zero )
        next_ops.a = '0;
      else
        next_ops.a = register_file.gpr_a;

    default:
      next_ops.a = register_file.gpr_a;
  ENDOPCMP
end

always_comb begin
  OPCMP(ir)
    MOVE_WITH_SYSTEM_REG_OPS:
      next_ops.b = sprin;

    OPXO(Xop_neg), OPXO(Xop_addze),
    OPXO(Xop_subfze):
      next_ops.b = '0;

    OPXO(Xop_addme), OPXO(Xop_subfme):
      next_ops.b = 32'hff_ff_ff_ff;

    default:
      if( predec_d.b_immediate )
        next_ops.b = immediate;
      else
        next_ops.b = register_file.gpr_b;
  ENDOPCMP
end

always_comb begin
  OPCMP(ir)
    MOVE_WITH_SYSTEM_REG_OPS:
      next_ops.c = register_file.msr;

    ROTATE_ANDING_OPS:
      next_ops.c = '0;

    OPX(Xop_srawi), OPX(Xop_sraw):
      next_ops.c = {DWIDTH{register_file.gpr_a[DWIDTH-1]}}; 

    default:
      next_ops.c = register_file.gpr_c;
  ENDOPCMP
end

//---------------------------------------------------------------------------
// Demultiplex special purpose register
//---------------------------------------------------------------------------
always_comb
  unique case(ir.xfx.spr)
    Spr_xer:    sprin = register_file.xer;
    Spr_ctr:    sprin = register_file.ctr;
    Spr_lnk:    sprin = register_file.lnk;
    Spr_srr0:   sprin = register_file.srr0;
    Spr_srr1:   sprin = register_file.srr1;
    Spr_csrr0:  sprin = register_file.csrr0;
    Spr_csrr1:  sprin = register_file.csrr1;
    Spr_dear:   sprin = register_file.dear;
    Spr_esr:    sprin = register_file.esr;
    Spr_mcsrr0: sprin = register_file.mcsrr0;
    Spr_mcsrr1: sprin = register_file.mcsrr1;
    Spr_gin:    sprin = register_file.gin;
    Spr_gout:   sprin = register_file.gout;
    Spr_goe:    sprin = register_file.goe;
    Spr_tsr:    sprin = timer.tsr;
    Spr_tcr:    sprin = timer.tcr;
    Spr_dec:    sprin = timer.dec;
    Spr_decar:  sprin = timer.decar;
    Spr_tbu:    sprin = timer.tbu;
    Spr_tbl:    sprin = timer.tbl;
    default:    sprin = 'x;
  endcase
//---------------------------------------------------------------------------
// Generate carry input
//---------------------------------------------------------------------------
always_comb
begin
  unique case(ir.d.opcd)
    Op_cmpi, Op_cmpli:
      next_ops.cin = 1'b1;

    Op_subfic:
      next_ops.cin = 1'b1;

    Op_alu_xo: begin
      unique casez(ir.x.xo)
        {1'bz, Xop_subfc}, {1'bz, Xop_subf}, Xop_cmp, Xop_cmpl, {1'bz, Xop_neg}:
          next_ops.cin = 1'b1;

        {1'bz, Xop_adde}, {1'bz, Xop_addme}, {1'bz, Xop_addze},
        {1'bz, Xop_subfe}, {1'bz, Xop_subfme}, {1'bz, Xop_subfze}:
          next_ops.cin = register_file.xer[XER_CA];

        default:
          next_ops.cin = 1'b0;
      endcase
    end

    default:
      next_ops.cin = 1'b0;
  endcase
end

//---------------------------------------------------------------------------
// Extract immediate value from instruction
//---------------------------------------------------------------------------
always_comb
begin
  immediate = 32'b0;

  unique case(ir.d.opcd)
    // sign-extended immediate
    Op_addi, Op_addic, Op_addic_rec, Op_subfic,
    Op_lwz, Op_stw, Op_cmpi, Op_lhz, Op_lbz, Op_stb, Op_sth,
    Op_lwzu, Op_stwu, Op_lhzu, Op_lbzu, Op_stbu, Op_sthu,
    Op_mulli:
      immediate = { {(DWIDTH-16){ir.d.d[15]}}, ir.d.d };

    // shifted immediate (sign-extension)
    /*Op_addis: begin
      immediate[31:16] = ir.d.d;
      //immediate[DWIDTH-1:32] = ir.d.d[31] ? '1 : '0;
      hardcoded_DWIDTH: assert(DWIDTH == 32);
      immediate[15:0] = '0;
    end*/

    // shifted immediate
    Op_addis, Op_andis, Op_oris, Op_xoris: begin
      //immediate[DWIDTH-1:32] <= '0;

      // synopsys translate_off
      hardcoded_DWIDTH_2: assert(DWIDTH == 32);
      // synopsys translate_on
      
      immediate[31:16] = ir.d.d;
      immediate[15:0] = '0;
    end

    Op_lmw, Op_stmw: begin
      immediate = { {(DWIDTH-16){ir.d.d[15]}}, ir.d.d } 
        + { {(DWIDTH-$bits(Reg_index)-2){1'b0}}, (predec_d.rt - ir.d.rt), 2'b00 };
    end

    // no sign-extension
    default:
      immediate = { 16'h0000, ir.d.d };
  endcase
end

//---------------------------------------------------------------------------
// Output register
//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    ops.a <= '0;
    ops.b <= '0;
    ops.c <= '0;
    ops.cin <= 1'b0;
    ops.cr <= '0;
  end else begin
    ops <= next_ops;
  end

endmodule


//---------------------------------------------------------------------------
//---------------------------------------------------------------------------
//---------------------------------------------------------------------------
//---------------------------------------------------------------------------


//module Operand_fetch
	//(	input logic clk, reset,
		//Register_file_if.read   register_file,
		//Timer_if.pu             timer,
		//Decode_data_if.decode   data,

		////Alu_data_if.decode                 alu,
		//Fixedpoint_data_if.op_fetch        fixedpoint,
		//Branch_data_if.decode              branch,
		//Trap_data_if.decode                trap,
		//Load_store_data_if.decode          load_store,
		//Write_back_data_if.decode          write_back,
	
		//Data_hazard_ctrl_if.operand_fetch  data_hazard);

//Word           immediate;
//Word           alu_a, alu_b;
//logic          alu_cin;
//logic          ra_is_zero;
//logic[4:0]     alu_rot_dist;
//logic[4:0]     alu_rot_start;
//logic[4:0]     alu_rot_stop;
//Word           sprin;
//Word           trap_a, trap_b;
//Msr            spreu_msrin;

//// forward counter and condition register
//assign branch.ctr = register_file.ctr;
//assign branch.cr = register_file.cr;
////assign
	////fixedpoint.alu_cr = register_file.cr,
	////fixedpoint.spreu_cr = register_file.cr;

////---------------------------------------------------------------------------
//// detect RA == 0 for instructions using RA|0
////---------------------------------------------------------------------------
//always_comb 
	//if( data.inst.d.ra == 0 ) 
		//ra_is_zero = 1'b1;
	//else
		//ra_is_zero = 1'b0;
////---------------------------------------------------------------------------
//// Select ALU argument inputs
////---------------------------------------------------------------------------

//// NOTE: synplify warns about this process not inferring combinational logic,
//// but the resulting schematic looks ok.
//[>* prepare immediate from instruction <]
//always_comb
//begin
	//immediate = 32'b0;

	//unique case(data.inst.d.opcd)
		//// sign-extended immediate
		//Op_addi, Op_addic, Op_addic_rec, Op_subfic,
		//Op_lwz, Op_stw, Op_cmpi, Op_lhz, Op_lbz, Op_stb, Op_sth,
		//Op_lwzu, Op_stwu, Op_lhzu, Op_lbzu, Op_stbu, Op_sthu,
		//Op_mulli:
			//immediate = { {(DWIDTH-16){data.inst.d.d[15]}}, data.inst.d.d };

		//// shifted immediate (sign-extension)
		//[>Op_addis: begin
			//immediate[31:16] = data.inst.d.d;
			////immediate[DWIDTH-1:32] = data.inst.d.d[31] ? '1 : '0;
			//hardcoded_DWIDTH: assert(DWIDTH == 32);
			//immediate[15:0] = '0;
		//end*/

		//// shifted immediate
		//Op_addis, Op_andis, Op_oris, Op_xoris: begin
			////immediate[DWIDTH-1:32] <= '0;

			//// synopsys translate_off
			//hardcoded_DWIDTH_2: assert(DWIDTH == 32);
			//// synopsys translate_on
			
			//immediate[31:16] = data.inst.d.d;
			//immediate[15:0] = '0;
		//end

		//// no sign-extension
		//default:
			//immediate = { 16'h0000, data.inst.d.d };
	//endcase
//end

////---------------------------------------------------------------------------
//// select inputs to ALU
////---------------------------------------------------------------------------
//// TODO writing of data_hazard.fu_? should be moved to a new process
//always_comb
//begin
	//// fu_a to fu_c set the destination functional unit port data from GPR
	//// ports A, B or C is sent to. The rotate instructions read port B, but
	//// not for ALU B. All other instructions use the default assignment.
	//data_hazard.fu_a = Fup_alu_a;
	//data_hazard.fu_b = Fup_alu_b;
	//data_hazard.fu_c = Fup_ls_din;
	//alu_a = register_file.gpr_a;
	//alu_b = register_file.gpr_b;

	//unique case(data.inst.xo.opcd)
		//Op_twi:
		//begin
			//data_hazard.fu_a = Fup_other;
		//end

		//// instructions using RA|0
		//Op_addi, Op_addis, Op_lwz, Op_stw, Op_lbz, Op_stb, Op_lhz, Op_sth,
		//Op_lwzu, Op_stwu, Op_lbzu, Op_stbu, Op_lhzu, Op_sthu,
		//Op_lmw, Op_stmw:
		//begin
			//if( ra_is_zero )
				//alu_a = 0;
			//else
				//alu_a = register_file.gpr_a;

			//alu_b = immediate;
		//end

		//Op_addic, Op_addic_rec, Op_subfic,
		//Op_cmpi, Op_cmpli, Op_mulli:
		//begin
			//alu_a = register_file.gpr_a;
			//alu_b = immediate;
		//end

		//Op_ori, Op_oris, Op_xori, Op_xoris, Op_andi, Op_andis:
		//begin
			//alu_a = register_file.gpr_c;
			//alu_b = immediate;
		//end

		//Op_branch:
		//begin
			//if( data.inst.i.aa )
				//alu_b = '0;
			//else
				//alu_b = data.pc;

			//alu_a[23:0] = data.inst.i.li[23:0];
			//alu_a[31:24] = (data.inst.i.li[23]) ? '1 : '0;
		//end

		//Op_bc:
		//begin
			//if( data.inst.i.aa )
				//alu_b = '0;
			//else
				//alu_b = data.pc;

			//alu_a[13:0] = data.inst.b.bd[13:0];
			//alu_a[31:14] = (data.inst.b.bd[13]) ? '1 : '0;
		//end

		//Op_bclr:
		//begin
			//unique case(data.inst.xl.xo)
				//Xxop_bclr: begin
					//alu_a = register_file.lnk;
					//alu_b = '0;
				//end

				//Xxop_bcctr: begin
					//alu_a = register_file.ctr;
					//alu_b = '0;
				//end

				//Xxop_rfi: begin
					//alu_a = {2'b0, register_file.srr0[DWIDTH-1:2]};
					//alu_b = '0;
				//end

				//Xxop_rfci: begin
					//alu_a = {2'b0, register_file.csrr0[DWIDTH-1:2]};
					//alu_b = '0;
				//end

				//Xxop_rfmci: begin
					//alu_a = {2'b0, register_file.mcsrr0[DWIDTH-1:2]};
					//alu_b = '0;
				//end

				//default: begin
					//alu_a = register_file.gpr_a;
					//alu_b = register_file.gpr_b;
				//end
			//endcase
		//end

		//Op_rlwimi: begin
			//alu_a = register_file.gpr_c;
			//alu_b = register_file.gpr_a;
		//end

		//Op_rlwinm, Op_rlwnm: begin
			//alu_a = register_file.gpr_c;
			//alu_b = '0;
			//data_hazard.fu_b = Fup_other;
		//end

		//Op_alu_xo: begin
			//unique casez(data.inst.x.xo)
				//Xop_tw: 
				//begin
					//data_hazard.fu_a = Fup_other;
					//data_hazard.fu_b = Fup_other;
				//end

				//{1'bz, Xop_addme}, {1'bz, Xop_subfme}:
				//begin
					//alu_a = register_file.gpr_a;
					//alu_b = '1;
				//end

				//{1'bz, Xop_addze}, {1'bz, Xop_subfze}, 
				//{1'bz, Xop_neg}:
				//begin
					//alu_a = register_file.gpr_a;
					//alu_b = '0;
					//data_hazard.fu_b = Fup_other;
				//end

				//Xop_slw, Xop_srw, Xop_popcb, Xop_prtyw,
				//Xop_mtocrf, Xop_mfocrf, Xop_mtspr:
				//begin
					//alu_a = register_file.gpr_c;
					//alu_b = '0;
					//data_hazard.fu_b = Fup_other;
				//end

				//Xop_sraw, Xop_srawi: begin
					//alu_a = register_file.gpr_c;
					//alu_b = {DWIDTH{register_file.gpr_c[$left(register_file.gpr_c)]}};
					//data_hazard.fu_a = Fup_other;  // XXX hack to disable forwarding to port A, because it is also used for alu_b
					//data_hazard.fu_b = Fup_other;
				//end

				//Xop_lwzx, Xop_lhzx, Xop_lbzx,
				//Xop_stwx, Xop_sthx, Xop_stbx,
				//Xop_lwzux, Xop_lhzux, Xop_lbzux,
				//Xop_stwux, Xop_sthux, Xop_stbux:
				//begin
					//if( ra_is_zero )
						//alu_a = '0;
					//else
						//alu_a = register_file.gpr_a;

					//alu_b = register_file.gpr_b;
				//end

				//Xop_and, Xop_andc, Xop_or, Xop_orc, Xop_xor, 
				//Xop_nand, Xop_nor, Xop_eqv, Xop_extsb, Xop_extsh,
				//Xop_mtmsr:
				//begin
					//alu_a = register_file.gpr_c;
					//alu_b = register_file.gpr_b;
				//end

				//default: begin
					//alu_a = register_file.gpr_a;
					//alu_b = register_file.gpr_b;
				//end
			//endcase
		//end

		//default:
		//begin
			//alu_a = register_file.gpr_a;
			//alu_b = register_file.gpr_b;
		//end
	//endcase
//end

////---------------------------------------------------------------------------
//// Generate carry input to ALU
////---------------------------------------------------------------------------
//always_comb
//begin
	//unique case(data.inst.d.opcd)
		//Op_cmpi, Op_cmpli:
			//alu_cin = 1'b1;

		//Op_subfic:
			//alu_cin = 1'b1;

		//Op_alu_xo: begin
			//unique casez(data.inst.x.xo)
				//{1'bz, Xop_subfc}, {1'bz, Xop_subf}, Xop_cmp, Xop_cmpl, {1'bz, Xop_neg}:
					//alu_cin = 1'b1;

				//{1'bz, Xop_adde}, {1'bz, Xop_addme}, {1'bz, Xop_addze},
				//{1'bz, Xop_subfe}, {1'bz, Xop_subfme}, {1'bz, Xop_subfze}:
					//alu_cin = register_file.xer[XER_CA];

				//default:
					//alu_cin = 1'b0;
			//endcase
		//end

		//default:
			//alu_cin = 1'b0;
	//endcase
//end

////---------------------------------------------------------------------------
//// Generate shift/rotate signals to Rotm 
////---------------------------------------------------------------------------
//always_comb
//begin : ctrl_rotl
	//logic[15:0] cop;

	//alu_rot_dist  = 5'b00000;
	//alu_rot_start = 5'b00000;
	//alu_rot_stop  = 5'b00000;

	//cop = {data.inst.x.opcd, data.inst.x.xo};
	//unique casez(cop)
		//{Op_rlwimi, 10'bzzzzzzzzzz},
		//{Op_rlwinm, 10'bzzzzzzzzzz}: begin
			//alu_rot_dist  = data.inst.m.rb;
			//alu_rot_start = data.inst.m.mb;
			//alu_rot_stop  = data.inst.m.me;
		//end

		//{Op_rlwnm, 10'bzzzzzzzzzz}: begin
			//alu_rot_dist  = register_file.gpr_b[4:0];
			//alu_rot_start = data.inst.m.mb;
			//alu_rot_stop  = data.inst.m.me;
		//end

		//{Op_alu_xo, Xop_slw}: begin
			//alu_rot_dist  = register_file.gpr_b[4:0];
			//alu_rot_start = 5'b00000;
			//alu_rot_stop  = 31 - register_file.gpr_b[4:0];
		//end

		//{Op_alu_xo, Xop_srw}: begin
			//alu_rot_dist  = 32 - register_file.gpr_b[4:0];
			//alu_rot_start = register_file.gpr_b[4:0];
			//alu_rot_stop  = 5'b11111;
		//end

		//{Op_alu_xo, Xop_srawi}: begin
			//alu_rot_dist  = 32 - data.inst.x.rb;
			//alu_rot_start = data.inst.x.rb;
			//alu_rot_stop  = 5'b11111;
		//end

		//{Op_alu_xo, Xop_sraw}: begin
			//alu_rot_dist  = 32 - register_file.gpr_b[4:0];
			//alu_rot_start = register_file.gpr_b[4:0];
			//alu_rot_stop  = 5'b11111;
		//end

		//default: begin
		//end
	//endcase
//end : ctrl_rotl

////---------------------------------------------------------------------------
//// Demultiplex special purpose register
////---------------------------------------------------------------------------
//always_comb
	//unique case(data.inst.xfx.spr)
		//Spr_xer:    sprin = register_file.xer;
		//Spr_ctr:    sprin = register_file.ctr;
		//Spr_lnk:    sprin = register_file.lnk;
		//Spr_srr0:   sprin = register_file.srr0;
		//Spr_srr1:   sprin = register_file.srr1;
		//Spr_csrr0:  sprin = register_file.csrr0;
		//Spr_csrr1:  sprin = register_file.csrr1;
		//Spr_dear:   sprin = register_file.dear;
		//Spr_esr:    sprin = register_file.esr;
		//Spr_mcsrr0: sprin = register_file.mcsrr0;
		//Spr_mcsrr1: sprin = register_file.mcsrr1;
		//Spr_gin:    sprin = register_file.gin;
		//Spr_gout:   sprin = register_file.gout;
		//Spr_tsr:    sprin = timer.tsr;
		//Spr_tcr:    sprin = timer.tcr;
		//Spr_dec:    sprin = timer.dec;
		//Spr_decar:  sprin = timer.decar;
		//Spr_tbu:    sprin = timer.tbu;
		//Spr_tbl:    sprin = timer.tbl;
		////default:    sprin = '0;
		//default:    sprin = 'x;
	//endcase


////---------------------------------------------------------------------------
//// Select input to trap unit
////---------------------------------------------------------------------------
//always_comb 
//begin
	//// default assignment
	//trap_a = '0;
	//trap_b = '0;

	//if( data.inst.d.opcd == Op_twi ) begin
		//trap_a = register_file.gpr_a;
		//trap_b = { {16{data.inst.d.d[15]}}, data.inst.d.d };
	//end else if( data.inst.d.opcd == Op_alu_xo && data.inst.x.xo == Xop_tw ) begin
		//trap_a = register_file.gpr_a;
		//trap_b = register_file.gpr_b;
	//end
//end

////---------------------------------------------------------------------------
//// MSR input to SPREU
////---------------------------------------------------------------------------
//always_comb spreu_msrin = register_file.msr;

////---------------------------------------------------------------------------
//// Datapath output register
////---------------------------------------------------------------------------
//always_ff @(posedge clk or posedge reset)
	//if( reset ) begin
		//fixedpoint.alu_a_in <= '0;
		//fixedpoint.alu_b_in <= '0;
		//fixedpoint.alu_cin <= 1'b0;
		//fixedpoint.alu_cr_in <= '0;
		//fixedpoint.rotm_x_in <= '0;
		//fixedpoint.rotm_q_in <= '0;
		//fixedpoint.rotm_sh <= '0;
		//fixedpoint.rotm_ma <= '0;
		//fixedpoint.rotm_mb <= '0;
		//fixedpoint.mul_a_in <= '0;
		//fixedpoint.mul_b_in <= '0;
		//fixedpoint.div_a_in <= '0;
		//fixedpoint.div_b_in <= '0;
		//fixedpoint.spreu_a_in <= '0;
		//fixedpoint.spreu_sprin <= '0;
		//fixedpoint.spreu_cr_in <= '0;
		//fixedpoint.spreu_msrin <= '0;
		////fixedpoint.set_zero();
		//trap.a <= '0;
		//trap.b <= '0;
		//write_back.lnk <= '0;
		//load_store.din <= '0;
	//end else begin
		//// default assignment
		//fixedpoint.alu_a_in <= '0;
		//fixedpoint.alu_b_in <= '0;
		//fixedpoint.alu_cin <= 1'b0;
		//fixedpoint.alu_cr_in <= '0;
		//fixedpoint.rotm_x_in <= '0;
		//fixedpoint.rotm_q_in <= '0;
		//fixedpoint.rotm_sh <= '0;
		//fixedpoint.rotm_ma <= '0;
		//fixedpoint.rotm_mb <= '0;
		//fixedpoint.mul_a_in <= '0;
		//fixedpoint.mul_b_in <= '0;
		//fixedpoint.div_a_in <= '0;
		//fixedpoint.div_b_in <= '0;
		//fixedpoint.spreu_a_in <= '0;
		//fixedpoint.spreu_sprin <= '0;
		//fixedpoint.spreu_cr_in <= '0;
		//fixedpoint.spreu_msrin <= '0;
		////fixedpoint.set_zero();
		//write_back.lnk <= '0;
		//load_store.din <= '0;

		//fixedpoint.alu_a_in <= alu_a;
		//fixedpoint.alu_b_in <= alu_b;
		//fixedpoint.alu_cin <= alu_cin;

		//// TODO change these and add rotm signals
		//fixedpoint.rotm_x_in <= alu_a;
		//fixedpoint.rotm_q_in <= alu_b;
		//fixedpoint.rotm_sh <= alu_rot_dist;
		//fixedpoint.rotm_ma <= alu_rot_start;
		//fixedpoint.rotm_mb <= alu_rot_stop;
		//fixedpoint.spreu_a_in <= alu_a;
		//fixedpoint.spreu_sprin <= sprin;
		//fixedpoint.spreu_msrin <= spreu_msrin;
		//fixedpoint.mul_a_in <= alu_a;
		//fixedpoint.mul_b_in <= alu_b;
		//fixedpoint.div_a_in <= alu_a;
		//fixedpoint.div_b_in <= alu_b;

		//fixedpoint.alu_cr_in <= register_file.cr;
		//fixedpoint.spreu_cr_in <= register_file.cr;

		//trap.a <= trap_a;
		//trap.b <= trap_b;

		//load_store.din <= register_file.gpr_c;
		//write_back.lnk <= data.npc;
	//end

//endmodule



// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
