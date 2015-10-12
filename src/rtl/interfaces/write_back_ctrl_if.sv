// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Pu_types::*;

interface Write_back_ctrl_if
	(	input clk,
		input reset );

	logic en, en_int;
	logic dis_ex, dis_ls;  // disable write-enables in execute or load store stage
	logic dis_sleep;       // disable sleep

	// written in DC
	Reg_index  gpr_dest_alu;
	Reg_index  gpr_dest_mem;
	logic      gpr_wr_alu; // store result from ALU
	logic      gpr_wr_mem; // store result from memory
	logic      wr_cr;      // store CR field verbatim
	logic[7:0] record_cr;  // record conditions bits after arithmetic/logic 
	                       // instructions / doubles as select for CR 
						   // operations
	logic      record_ca;
	logic      record_ov;

	logic         spr_we;
	logic[9:0]    spr_sel;

	logic         msr_we;

	logic         sleep;   // put the complete processor to sleep

	// read in WB
	Reg_index     wb_gpr_dest_alu;
	Reg_index     wb_gpr_dest_mem;
	logic         wb_gpr_wr_alu;
	logic         wb_gpr_wr_mem;
	logic         wb_wr_cr;
	logic[7:0]    wb_record_cr;
	logic         wb_record_ca;
	logic         wb_record_ov;
	logic         wb_spr_we;
	logic[9:0]    wb_spr_sel;
	logic         wb_msr_we;
	logic         wb_sleep;

	// --- internal variables ---
	Reg_index     gpr_dest_alu_d1;
	Reg_index     gpr_dest_mem_d1;
	logic         gpr_wr_alu_d1;
	logic         gpr_wr_mem_d1;
	logic         wr_cr_d1;
	logic[7:0]    record_cr_d1;
	logic         record_ca_d1;
	logic         record_ov_d1;
	logic         spr_we_d1;
	logic[9:0]    spr_sel_d1;
	logic         msr_we_d1;
	logic         sleep_d1;


	always_ff @(posedge clk or posedge reset)
	begin : delay
		if( reset ) begin
			wb_gpr_dest_alu <= '0;
			wb_gpr_dest_mem <= '0;
			wb_gpr_wr_alu <= '0;
			wb_gpr_wr_mem <= '0;
			wb_record_cr <= '0;
			gpr_dest_alu_d1 <= '0;
			gpr_dest_mem_d1 <= '0;
			wr_cr_d1 <= '0;
			record_cr_d1 <= '0;
			record_ca_d1 <= '0;
			record_ov_d1 <= '0;
			spr_we_d1 <= 1'b0;
			wb_spr_we <= 1'b0;
			spr_sel_d1 <= '0;
			wb_spr_sel <= '0;
			gpr_wr_alu_d1 <= '0;
			gpr_wr_mem_d1 <= '0;
			wb_gpr_wr_alu <= '0;
			wb_gpr_wr_mem <= '0;
			wb_wr_cr <= '0;
			wb_record_ov <= '0;
			wb_record_ca <= '0;
			msr_we_d1 <= 1'b0;
			wb_msr_we <= 1'b0;
			sleep_d1 <= 1'b0;
			wb_sleep <= 1'b0;
		end else begin
			if( !dis_ex ) begin
				gpr_wr_alu_d1 <= gpr_wr_alu;
				gpr_wr_mem_d1 <= gpr_wr_mem;
				record_cr_d1 <= record_cr;
				record_ca_d1 <= record_ca;
				record_ov_d1 <= record_ov;
				spr_we_d1 <= spr_we;
				msr_we_d1 <= msr_we;
				sleep_d1 <= sleep;
			end else begin
				gpr_wr_alu_d1 <= 1'b0;
				gpr_wr_mem_d1 <= 1'b0;
				record_cr_d1 <= '0;
				record_ca_d1 <= 1'b0;
				record_ov_d1 <= 1'b0;
				spr_we_d1 <= 1'b0;
				msr_we_d1 <= 1'b0;
				sleep_d1 <= 1'b0;
			end

			gpr_dest_alu_d1 <= gpr_dest_alu;
			gpr_dest_mem_d1 <= gpr_dest_mem;
			wr_cr_d1 <= wr_cr;
			spr_sel_d1 <= spr_sel;


			if( !dis_ls ) begin
				wb_gpr_wr_alu <= gpr_wr_alu_d1;
				wb_gpr_wr_mem <= gpr_wr_mem_d1;
				wb_record_cr <= record_cr_d1;
				wb_record_ca <= record_ca_d1;
				wb_record_ov <= record_ov_d1;
				wb_spr_we <= spr_we_d1;
				wb_msr_we <= msr_we_d1;
				wb_sleep <= sleep_d1;
			end else begin
				wb_gpr_wr_alu <= 1'b0;
				wb_gpr_wr_mem <= 1'b0;
				wb_record_cr <= '0;
				wb_record_ca <= 1'b0;
				wb_record_ov <= 1'b0;
				wb_spr_we <= 1'b0;
				wb_msr_we <= 1'b0;
				wb_sleep <= 1'b0;
			end

			wb_gpr_dest_alu <= gpr_dest_alu_d1;
			wb_gpr_dest_mem <= gpr_dest_mem_d1;
			wb_wr_cr <= wr_cr_d1;
			wb_spr_sel <= spr_sel_d1;
		end
	end : delay

	assign en = en_int;

	/*task automatic decode_set_zero;
		gpr_dest_alu = '0;
		gpr_dest_mem = '0;
		gpr_wr_alu = '0;
		gpr_wr_mem = '0;
		wr_cr = 1'b0;
		record_cr = '0;
		record_ca = '0;
		record_ov = '0;
		spr_we = 1'b0;
		spr_sel = '0;
		msr_we = 1'b0;
	endtask*/

	modport decode
		(	//import decode_set_zero,
			output gpr_dest_alu, 
			output gpr_dest_mem, 
			output gpr_wr_alu,
			output gpr_wr_mem,
			output wr_cr,
			output record_cr,
			output record_ca,
			output record_ov,
			output spr_we,
			output spr_sel,
			output msr_we,
			output sleep );

	modport write_back 
		(	input en,
			input wb_gpr_dest_alu, 
			input wb_gpr_dest_mem, 
			input wb_gpr_wr_alu,
			input wb_gpr_wr_mem,
			input wb_wr_cr,
			input wb_record_cr,
			input wb_record_ca,
			input wb_record_ov,
			input wb_spr_we,
			input wb_spr_sel,
			input wb_msr_we,
			input wb_sleep,
      input dis_sleep );

	modport int_sm ( 
		output dis_ex, dis_ls, dis_sleep,
		output en_int
	);

endinterface


// vim: noexpandtab ts=4 sw=4 softtabstop=0 nosmarttab:
