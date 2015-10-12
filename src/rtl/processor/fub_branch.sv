// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Fub_branch
  ( input logic clk, reset,
    input Frontend::Issue_slot inst,
    input logic predicted_taken,
    input logic disable_wb,
    input Pu_types::Word lnk,
    input Pu_types::Word ctr,
    input Pu_types::Word srr0, csrr0, mcsrr0,
    input Pu_types::Cr_bits cr,
    Operand_if.read opbus,

    output Backend::Result_bus resbus,
    output Frontend::Branch_control bctrl,
    Int_sched_if.trap except );

import Pu_types::*;
import Pu_inst::*;
import Backend::*;
import Frontend::*;

//Branch_data_if branch_data();
//Trap_ctrl_if trap_ctrl();
//Trap_data_if trap_data();


//Dec_trap dec_trap (
  //.clk, .reset,
  //.inst,
  //.ctrl(trap_ctrl)
//);


//assign
  //trap_data.a = opbus.opbus[inst.thread].a,
  //trap_data.b = opbus.opbus[inst.thread].b;



//Trap trap (
  //.clk(clk),
  //.reset(reset),
  //.ctrl(trap_ctrl.trap),
  //.data(trap_data.trap),
  //.except(int_sched_if.trap)
//);


//---------------------------------------------------------------------------
// Branching logic
//---------------------------------------------------------------------------
Inst ir;
Thread_id thread_d;
Address pc_d, pc_d2;
//Word ctr, next_ctr;
Word next_ctr;
//Word lnk;
Word imm;
//Condition_register cr;
logic ctr_ok;
logic cond_ok;
Branch_control next_bctrl;
logic      br_jump;
logic[4:0] br_crbi;
logic      br_cond;
logic      br_mask_cond;
logic      br_ctr_eq;
logic      br_mask_ctr;
logic      br_dec_ctr;
logic      br_save_lnk;
logic      br_to_lnk;
logic      br_to_ctr;
logic      br_abs;
logic      br_srr0;
logic      br_csrr0;
logic      br_mcsrr0;

logic      trap_en;
Trap_to    trap_to;
logic      base_trap;
Word       aa, bb;

logic      mispredicted;
logic      is_not_branch;

Address    pc_inc;

// performance counters for branch prediction
logic[31:0] cnt_branches;
logic[31:0] cnt_mis_taken;
logic[31:0] cnt_mis_not_taken;

assign ir = inst.ir;

// inputs from oberand bus
//assign lnk = opbus.opbus[inst.thread].a;
//assign imm = opbus.opbus[inst.thread].b;
//assign ctr = opbus.opbus[inst.thread].c;
//assign cr = opbus.opbus[inst.thread].cr;

//assign
  //aa = opbus.get_opbus_a(thread_d),
  //bb = opbus.get_opbus_b(thread_d);
assign
  aa = opbus.opbus_0.a,
  bb = opbus.opbus_0.b;

always_ff @(posedge clk)
begin
  thread_d <= inst.thread;
  pc_d <= inst.pc;
  pc_d2 <= pc_d;
end

//---------------------------------------------------------------------------
// Generate branch control signals
//---------------------------------------------------------------------------
always_comb
begin
  br_crbi = ir.b.bi;
  br_cond = ir.b.bo[3];
  br_mask_cond = ir.b.bo[4];
  br_ctr_eq = ir.b.bo[1];
  br_mask_ctr = ir.b.bo[2];
  br_save_lnk = ir.i.lk;

  // default assignments
  br_jump = 1'b0;
  br_dec_ctr = 1'b0;
  br_to_lnk = 1'b0;
  br_to_ctr = 1'b0;
  br_abs = 1'b0;
  br_srr0 = 1'b0;
  br_csrr0 = 1'b0;
  br_mcsrr0 = 1'b0;
  is_not_branch = 1'b0;

  unique case(ir.d.opcd)
    Op_branch: begin
      br_jump = 1'b1;
      br_dec_ctr = 1'b0;
      br_abs = ir.i.aa;
    end

    Op_bc: begin
      br_jump = 1'b0;
      br_dec_ctr = ~ir.b.bo[2];
      br_abs = ir.i.aa;
    end

    Op_bclr: begin
      case(ir.xl.xo)
        Xxop_bclr: begin
          br_jump = 1'b0;
          br_dec_ctr = ~ir.b.bo[2];
          br_to_lnk = 1'b1;
        end

        Xxop_bcctr: begin
          br_jump = 1'b0;
          br_dec_ctr = ~ir.b.bo[2];
          br_to_ctr = 1'b1;
        end

        Xxop_rfi: begin
          br_jump = 1'b1;
          br_save_lnk = 1'b0;
          br_srr0 = 1'b1;
        end

        Xxop_rfci: begin
          br_jump = 1'b1;
          br_save_lnk = 1'b0;
          br_csrr0 = 1'b1;
        end

        Xxop_rfmci: begin
          br_jump = 1'b1;
          br_save_lnk = 1'b0;
          br_mcsrr0 = 1'b1;
        end
      endcase
    end

    default: begin
      br_jump = 1'b0;
      br_dec_ctr = 1'b0;
      is_not_branch = 1'b1;
    end
  endcase
end

//---------------------------------------------------------------------------
// Branch datapath
//---------------------------------------------------------------------------

always_comb
begin : decrement_counter
  if( br_dec_ctr )
    next_ctr = ctr - 1;
  else
    next_ctr = ctr;
end : decrement_counter


assign cond_ok = br_mask_cond || (cr[br_crbi] == br_cond);
//assign ctr_ok = br_mask_ctr | ((next_ctr != 0) ^ br_ctr_eq);
//assign ctr_ok = br_mask_ctr | ((| next_ctr) ^ br_ctr_eq);
assign ctr_ok = br_mask_ctr | ((ctr != 32'h1) ^ br_ctr_eq);

assign mispredicted = !predicted_taken || (predicted_taken && (next_bctrl.jump_vec != inst.npc));

// disabled for synthesis, since no readout available yet.
`ifndef SYNTHESIS
/** Count mispredictions:
* cnt_mis_taken counts taken branches that where not predicted.
* cnt_mis_not_taken counts not taken branches that where predicted as taken.
* */
always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    cnt_branches <= '0;
    cnt_mis_taken <= '0;
    cnt_mis_not_taken <= '0;
  end else begin
    if( inst.valid ) begin
      cnt_branches <= cnt_branches + 1;

      if( !predicted_taken && (br_jump || (ctr_ok && cond_ok)) )
        cnt_mis_taken <= cnt_mis_taken + 1;

      if( !br_jump && !(ctr_ok && cond_ok) && predicted_taken )
        cnt_mis_not_taken <= cnt_mis_not_taken + 1;
    end
  end
`endif  /* SYNTHESIS */

always_comb begin
  // default assignment
  next_bctrl.jump = 1'b0;
  next_bctrl.fb_taken = 1'b0;
  next_bctrl.fb_not_taken = 1'b0;

  if( inst.valid && !is_not_branch ) begin
    if( br_jump ) begin
      next_bctrl.fb_taken = 1'b1;
      next_bctrl.jump = mispredicted;
    end else
      if( ctr_ok && cond_ok ) begin
        next_bctrl.fb_taken = 1'b1;
        next_bctrl.jump = mispredicted;
      end else begin
        next_bctrl.fb_not_taken = 1'b1;
        next_bctrl.jump = predicted_taken;  // jump if wrongly predicted
      end
  end else if( inst.valid && is_not_branch && predicted_taken ) begin
    // wrongfully predicted some instruction to be taken branch
    next_bctrl.jump = 1'b1;
    next_bctrl.fb_not_taken = 1'b1;
  end
end

// destination address calculation (PC or 0  +  immediate or LNK or CTR)
always_comb begin
  logic false_positive;

  false_positive = (predicted_taken && (!br_jump && !(ctr_ok && cond_ok)))
    || (inst.valid && is_not_branch && predicted_taken);

  unique casez({false_positive, br_srr0, br_csrr0, br_mcsrr0, br_to_lnk,
      br_to_ctr, br_abs})
    7'b1zz_zzzz: next_bctrl.jump_vec = inst.pc + 1;
    7'b010_0000: next_bctrl.jump_vec = {2'b0, srr0[$left(srr0):2]};
    7'b001_0000: next_bctrl.jump_vec = {2'b0, csrr0[$left(csrr0):2]};
    7'b000_1000: next_bctrl.jump_vec = {2'b0, mcsrr0[$left(mcsrr0):2]};
    7'b000_0100: next_bctrl.jump_vec = {2'b0, lnk[$left(lnk):2]};
    7'b000_0010: next_bctrl.jump_vec = {2'b0, ctr[$left(ctr):2]};
    7'b000_0001: next_bctrl.jump_vec = imm;
    7'b000_0000: next_bctrl.jump_vec = inst.pc + imm;
    default: begin
      //check_branch_target_select: assert(0);
      next_bctrl.jump_vec = 'x;
    end
  endcase

  //if( (predicted_taken && (!br_jump && !(ctr_ok && cond_ok)))
    //|| (inst.valid && is_not_branch && predicted_taken) )  // false positive
  ////if( predicted_taken && (next_bctrl.fb_not_taken) )  // false positive
    //next_bctrl.jump_vec = inst.pc + 1;
  //else if( br_srr0 )
    //next_bctrl.jump_vec = {2'b0, srr0[$left(srr0):2]};
  //else if( br_csrr0 )
    //next_bctrl.jump_vec = {2'b0, csrr0[$left(csrr0):2]};
  //else if( br_mcsrr0 )
    //next_bctrl.jump_vec = {2'b0, mcsrr0[$left(mcsrr0):2]};
  //else if( br_to_lnk )
    //next_bctrl.jump_vec = {2'b0, lnk[$left(lnk):2]};
  //else if( br_to_ctr )
    //next_bctrl.jump_vec = {2'b0, ctr[$left(ctr):2]};
  //else begin
    //if( br_abs )
      //next_bctrl.jump_vec = imm;
    //else
      //next_bctrl.jump_vec = inst.pc + imm;
  //end
end

always_comb begin
  if( ir.i.opcd == Op_branch )
    imm = { {(DWIDTH-24){ir.i.li[23]}}, ir.i.li };
  else
    imm = { {(DWIDTH-14){ir.b.bd[13]}}, ir.b.bd };
end

assign
  next_bctrl.fb_pc = inst.pc;

assign except.rest_base = br_srr0;
assign except.rest_crit = br_csrr0;
assign except.rest_mcheck = br_mcsrr0;

//---------------------------------------------------------------------------
// Output registers for branch logic
//---------------------------------------------------------------------------

assign pc_inc = inst.pc +1;


assign resbus.valid = 1'b1;

always_ff @(posedge clk)
begin : reg_ctr
  resbus.res_a <= next_ctr;
  //resbus.res_b <= inst.npc;
  resbus.res_b <= {pc_inc[$left(pc_inc)-2:0], 2'b00};

  resbus.crf <= '0;
  resbus.msr <= '0;
  resbus.cout <= 1'b0;
  resbus.ov <= 1'b0;
end : reg_ctr

//always_ff @(posedge clk or posedge reset)
  //if( reset ) begin
    //bctrl.jump <= 1'b0;
    //bctrl.jump_vec <= '0;
    //bctrl.fb_taken <= 1'b0;
    //bctrl.fb_not_taken <= 1'b0;
    //bctrl.fb_pc <= 1'b0;
  //end else begin
    //bctrl <= next_bctrl;
  //end

assign bctrl = next_bctrl;


//---------------------------------------------------------------------------
// Trap control signals
//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    trap_en <= 1'b0;
    trap_to <= 'x;
  end else begin
    //default assignment
    trap_en <= 1'b0;

    if( ((ir.x.opcd == Op_alu_xo) && (ir.x.xo == Xop_tw))
        || (ir.x.opcd == Op_twi) )
      trap_en <= 1'b1;

    trap_to <= ir.x.rt;
  end

//---------------------------------------------------------------------------
// Trap logic and output registers
//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		base_trap <= 1'b0;
	end else begin
		// default assignment
		base_trap <= 1'b0;

		if( trap_en ) begin
			if( trap_to.lts && (signed'(aa) < signed'(bb)) )
				base_trap <= 1'b1;

			if( trap_to.gts && (signed'(aa) > signed'(bb)) )
				base_trap <= 1'b1;

			if( trap_to.eq && (aa == bb) )
				base_trap <= 1'b1;

			if( trap_to.ltu && (aa < bb) )
				base_trap <= 1'b1;

			if( trap_to.gtu && (aa > bb) )
				base_trap <= 1'b1;
		end
	end


assign except.base_trap = base_trap & ~disable_wb;
assign except.pc_trap = pc_d2 & ~disable_wb;
//---------------------------------------------------------------------------


endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
