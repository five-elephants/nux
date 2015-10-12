// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


// TODO CR registers should be tracked with an optimized version of 
// Tag_shiftreg.

module Dhaz_tag_mem
	#(	parameter bit ONE_GPR_WRITE_PORT = 1'b1,
		parameter bit FORWARDING = 1'b1 )
	(	input logic clk, reset,

		Data_hazard_ctrl_if.data_hazard_ctrl  ctrl,
		Inst_fetch_ctrl_if.data_hazard_ctrl   if_ctrl,
		Decode_ctrl_if.data_hazard_ctrl       dc_ctrl,
		Bypass_if.control                     bypass );

import Pu_types::*;

// local parameters
localparam int TRACK_STAGES = 3;

// local types
typedef logic[$bits(Reg_index)-1:0] Gpr_tag;
typedef logic[1:0] Gpr_data;

// signals
logic    hold;
logic    shift;


logic    gpr_hold;
logic    cr_hold;
logic    ctr_hold;
logic    lnk_hold;
logic    xer_hold;
logic    spr_hold;

Bypass_line_ctrl  bypass_lines;
logic             bpon[0:2];

//---------------------------------------------------------------------------
/** Control logic for forwarding lines. Is called from always_comb blocks
* below */
function automatic void control_bypass(input logic read, src_alu, src_mem,
							logic index_alu[0:2], index_mem[0:2],
							Fu_port dest,
							inout logic bpon_i);
	if( read && ctrl.en ) begin
		// can only forward if the writing instruction is currently in EX
		if( src_alu && index_alu[0] ) begin
			bpon_i = 1'b1;

			case(dest)
				Fup_alu_a:   bypass_lines.fxdp_to_alu_a = 1'b1;
				Fup_alu_b:   bypass_lines.fxdp_to_alu_b = 1'b1;
				default:     bpon_i = 1'b0;
			endcase
		end

		// can only forward if the writing instruction is currently in LS
		/*if( src_mem && index_mem[1] ) begin
			bpon_i = 1'b1;

			case(dest)
				Fup_alu_a:   bypass_lines.ls_to_alu_a = 1'b1;
				Fup_alu_b:   bypass_lines.ls_to_alu_b = 1'b1;
				default:     bpon_i = 1'b0;
			endcase
		end*/
	end
endfunction
//---------------------------------------------------------------------------


// hold if enabled and hazards are present
assign hold = ctrl.en 
	& ( gpr_hold | cr_hold | ctr_hold | lnk_hold | xer_hold | spr_hold);
assign shift = 1'b1;

// output signals to instruction fetch and decode
assign if_ctrl.hold_data = hold;
assign dc_ctrl.hold_data = hold;

//---------------------------------------------------------------------------
/** Delay bypass network control signals for one cycle */
always_ff @(posedge clk or posedge reset)
	if( reset )
		//for(int i=0; i<$bits(bypass.lines); i++)
			//bypass.lines[i] <= 1'b0;
		bypass.lines <= '0;
	else
		bypass.lines <= bypass_lines;
//---------------------------------------------------------------------------


//---------------------------------------------------------------------------
generate if( ONE_GPR_WRITE_PORT ) begin : g_track_one_gpr_write_port
	Gpr_tag   gpr_tag;
	Gpr_data  gpr_datain;
	Gpr_data  gpr_dataout[0:2];
	Gpr_tag   gpr_test[0:2];
	logic     gpr_found[0:2];
	logic     gpr_index[0:2][0:TRACK_STAGES-1];

	Tag_shiftreg 
		#(	.TAG_SIZE($size(Gpr_tag)),
			.DATA_SIZE($size(Gpr_data)),
			.NUM_STAGES(TRACK_STAGES),
			.NUM_TESTPORTS(3) )
		gpr_tracker
		(	.clk(clk),
			.reset(reset),
			.shift(shift),
			.tag(gpr_tag),
			.tag_valid((ctrl.write_gpr_dest_alu | ctrl.write_gpr_dest_mem) & ~hold & ctrl.en),
			.datain(gpr_datain),
			.test(gpr_test),
			.found(gpr_found),
			.index(gpr_index),
			.dataout(gpr_dataout) );

	assign 
		gpr_test[0] = ctrl.gpr_a,
		gpr_test[1] = ctrl.gpr_b,
		gpr_test[2] = ctrl.gpr_c;

	always_comb
		if( ctrl.write_gpr_dest_mem ) begin
			gpr_tag = ctrl.gpr_dest_mem;
			gpr_datain = 2'b10;
		end else begin
			gpr_tag = ctrl.gpr_dest_alu;
			gpr_datain = 2'b01;
		end


	assign gpr_hold = 
			  (gpr_found[0] & ctrl.read_gpr_a) & ~bpon[0] 
			| (gpr_found[1] & ctrl.read_gpr_b) & ~bpon[1]
			| (gpr_found[2] & ctrl.read_gpr_c) & ~bpon[2];
	

	//---------------------------------------------------------------------------
	/** Generate bypass network control signals */
	if( FORWARDING ) begin : g_fwd_ctrl
		always_comb begin : bypass_control
			// default assignment
			//for(int i=0; i<$bits(bypass_lines); i++)
				//bypass_lines[i] = 1'b0;
			bypass_lines = '0;

			for(int i=0; i<$size(bpon); i++)
				bpon[i] = 1'b0;

			control_bypass(ctrl.read_gpr_a, 
				gpr_found[0] && (gpr_dataout[0] == 2'b01),
				gpr_found[0] && (gpr_dataout[0] == 2'b10),
				gpr_index[0],
				gpr_index[0],
				ctrl.fu_a,
				bpon[0]);

			control_bypass(ctrl.read_gpr_b, 
				gpr_found[1] && (gpr_dataout[1] == 2'b01),
				gpr_found[1] && (gpr_dataout[1] == 2'b10),
				gpr_index[1],
				gpr_index[1],
				ctrl.fu_b,
				bpon[1]);

			control_bypass(ctrl.read_gpr_c, 
				gpr_found[2] && (gpr_dataout[2] == 2'b01),
				gpr_found[2] && (gpr_dataout[2] == 2'b10),
				gpr_index[2],
				gpr_index[2],
				ctrl.fu_c,
				bpon[2]);
		end
	end : g_fwd_ctrl
	else
	begin : g_no_fwd_ctrl
		always_comb begin
			for(int i=0; i<$size(bpon); i++)
				bpon[i] = 1'b0;

			bypass_lines = '0;
		end
	end : g_no_fwd_ctrl
	//---------------------------------------------------------------------------
	
end else begin : g_track_two_gpr_write_ports
	Gpr_tag   gpr_alu_test[0:2];
	logic     gpr_alu_found[0:2];
	logic     gpr_alu_index[0:2][0:TRACK_STAGES-1];

	Tag_shiftreg 
		#(	.TAG_SIZE($size(Gpr_tag)),
			.NUM_STAGES(TRACK_STAGES),
			.NUM_TESTPORTS(3) )
		gpr_tracker_alu
		(	.clk(clk),
			.reset(reset),
			.shift(shift),
			.tag(ctrl.gpr_dest_alu),
			.tag_valid(ctrl.write_gpr_dest_alu & ~hold & ctrl.en),
			.datain(2'b0),
			.test(gpr_alu_test),
			.found(gpr_alu_found),
			.index(gpr_alu_index),
			.dataout() );

	assign 
		gpr_alu_test[0] = ctrl.gpr_a,
		gpr_alu_test[1] = ctrl.gpr_b,
		gpr_alu_test[2] = ctrl.gpr_c;



	Gpr_tag   gpr_mem_test[0:2];
	logic     gpr_mem_found[0:2];
	logic     gpr_mem_index[0:2][0:TRACK_STAGES-1];

	Tag_shiftreg 
		#(	.TAG_SIZE($bits(Reg_index)),
			.NUM_STAGES(TRACK_STAGES),
			.NUM_TESTPORTS(3) )
		gpr_tracker_mem
		(	.clk(clk),
			.reset(reset),
			.shift(shift),
			.tag(ctrl.gpr_dest_mem),
			.tag_valid(ctrl.write_gpr_dest_mem & ~hold & ctrl.en),
			.datain(2'b0),
			.test(gpr_mem_test),
			.found(gpr_mem_found),
			.index(gpr_mem_index),
			.dataout() );

	assign 
		gpr_mem_test[0] = ctrl.gpr_a,
		gpr_mem_test[1] = ctrl.gpr_b,
		gpr_mem_test[2] = ctrl.gpr_c;


	assign gpr_hold = 
		  ( (gpr_alu_found[0] | gpr_mem_found[0]) 
		     & ctrl.read_gpr_a & ~bpon[0] )
		| ( (gpr_alu_found[1] | gpr_mem_found[1])
		     & ctrl.read_gpr_b & ~bpon[1] )
		| ( (gpr_alu_found[2] | gpr_mem_found[2])
	         & ctrl.read_gpr_c & ~bpon[2] );


	//---------------------------------------------------------------------------
	/** Generate bypass network control signals */
	if( FORWARDING ) begin : g_fwd_ctrl
		always_comb begin : bypass_control
			// default assignment
			bypass_lines = '0;
			for(int ii=0; ii<$size(bpon); ii++)
				bpon[ii] = 1'b0;

			control_bypass(ctrl.read_gpr_a, 
				gpr_alu_found[0],
				gpr_mem_found[0],
				gpr_alu_index[0],
				gpr_mem_index[0],
				ctrl.fu_a,
				bpon[0]);

			control_bypass(ctrl.read_gpr_b, 
				gpr_alu_found[1],
				gpr_mem_found[1],
				gpr_alu_index[1],
				gpr_mem_index[1],
				ctrl.fu_b,
				bpon[1]);

			control_bypass(ctrl.read_gpr_c, 
				gpr_alu_found[2],
				gpr_mem_found[2],
				gpr_alu_index[2],
				gpr_mem_index[2],
				ctrl.fu_c,
				bpon[2]);
		end
	end : g_fwd_ctrl
	else
	begin : g_no_fwd_ctrl
		always_comb begin
			for(int i=0; i<$size(bpon); i++)
				bpon[i] = 1'b0;

			bypass_lines = '0;
		end
	end : g_no_fwd_ctrl
	//---------------------------------------------------------------------------

	
end : g_track_two_gpr_write_ports
endgenerate
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
//track CRs
logic[2:0] cr_tag;
logic[2:0] cr_test[0:2];
logic      cr_found[0:2];
logic      cr_index[0:2][0:TRACK_STAGES-1];

Tag_shiftreg 
	#(	.TAG_SIZE(3),
		.NUM_STAGES(TRACK_STAGES),
		.NUM_TESTPORTS(3) )
	cr_tracker
	(	.clk(clk),
		.reset(reset),
		.shift(shift),
		.tag(cr_tag),
		.tag_valid((| ctrl.write_cr) & ~hold & ctrl.en),
		.datain(2'b0),
		.test(cr_test),
		.found(cr_found),
		.index(cr_index),
		.dataout() );


function automatic logic[2:0] cr_idx_encode(input logic[7:0] sel);
	logic[2:0] rv;

	unique case(sel)
		8'b00000001: rv = 3'h0;
		8'b00000010: rv = 3'h1;
		8'b00000100: rv = 3'h2;
		8'b00001000: rv = 3'h3;
		8'b00010000: rv = 3'h4;
		8'b00100000: rv = 3'h5;
		8'b01000000: rv = 3'h6;
		8'b10000000: rv = 3'h7;
		default:     rv = 3'hx;
	endcase

	return rv;
endfunction

assign
	cr_tag = cr_idx_encode(ctrl.write_cr),
	cr_test[0] = cr_idx_encode(ctrl.read_cr_0),
	cr_test[1] = cr_idx_encode(ctrl.read_cr_1),
	cr_test[2] = cr_idx_encode(ctrl.read_cr_2);

assign cr_hold = ((| ctrl.read_cr_0) | (| ctrl.read_cr_1) | (| ctrl.read_cr_2)) 
	& (cr_found[0] | cr_found[1] | cr_found[2]);
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
//track CTR
logic     ctr_test[0:0];
logic     ctr_found[0:0];
logic     ctr_index[0:0][0:TRACK_STAGES-1];

Tag_shiftreg 
	#(	.TAG_SIZE(1),
		.NUM_STAGES(TRACK_STAGES),
		.NUM_TESTPORTS(1) )
	ctr_tracker
	(	.clk(clk),
		.reset(reset),
		.shift(shift),
		.tag(1'b1),
		.tag_valid(ctrl.write_ctr & ~hold & ctrl.en),
		.datain(2'b0),
		.test(ctr_test),
		.found(ctr_found),
		.index(ctr_index),
		.dataout() );

always_comb
	ctr_test[0] = 1'b1;

assign ctr_hold = ctr_found[0] & ctrl.read_ctr;
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// track other special purpose registers
logic[$bits(Spr_reduced)-1:0]  spr_test[0:1];
logic                          spr_found[0:1];
logic                          spr_index[0:1][0:TRACK_STAGES-1];

Tag_shiftreg
	#(	.TAG_SIZE($bits(Spr_reduced)),
		.NUM_STAGES(TRACK_STAGES),
		.NUM_TESTPORTS(2) )
	spr_tracker
	(	.clk(clk),
		.reset(reset),
		.shift(shift),
		.tag(ctrl.spr_dest),
		.tag_valid(ctrl.write_spr),
		.datain(2'b0),
		.test(spr_test),
		.found(spr_found),
		.index(spr_index),
		.dataout() );

always_comb
begin
	spr_test[0] = ctrl.spr_src;
	spr_test[1] = ctrl.spr_src2;
end

assign spr_hold = (spr_found[0] & ctrl.read_spr) | (spr_found[1] & ctrl.read_spr2);
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
//track LNK 
logic     lnk_test[0:0];
logic     lnk_found[0:0];
logic     lnk_index[0:0][0:TRACK_STAGES-1];

Tag_shiftreg 
	#(	.TAG_SIZE(1),
		.NUM_STAGES(TRACK_STAGES),
		.NUM_TESTPORTS(1) )
	lnk_tracker
	(	.clk(clk),
		.reset(reset),
		.shift(shift),
		.tag(1'b1),
		.tag_valid(ctrl.write_lnk & ~hold & ctrl.en),
		.datain(2'b0),
		.test(lnk_test),
		.found(lnk_found),
		.index(lnk_index),
		.dataout() );

always_comb
	lnk_test[0] = 1'b1;

assign lnk_hold = lnk_found[0] & ctrl.read_lnk;
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
//track XER 
logic     xer_test[0:0];
logic     xer_found[0:0];
logic     xer_index[0:0][0:TRACK_STAGES-1];

Tag_shiftreg 
	#(	.TAG_SIZE(1),
		.NUM_STAGES(TRACK_STAGES),
		.NUM_TESTPORTS(1) )
	xer_tracker
	(	.clk(clk),
		.reset(reset),
		.shift(shift),
		.tag(1'b1),
		.tag_valid(ctrl.write_xer & ~hold & ctrl.en),
		.datain(2'b0),
		.test(xer_test),
		.found(xer_found),
		.index(xer_index),
		.dataout() );

always_comb
	xer_test[0] = 1'b1;

assign xer_hold = xer_found[0] & ctrl.read_xer;
//---------------------------------------------------------------------------
endmodule
