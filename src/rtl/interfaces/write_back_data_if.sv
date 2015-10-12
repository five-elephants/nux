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

interface Write_back_data_if
	(	input clk,
		input reset );


	// written in EX
	Word res;
	logic cout;
	Cr_field cr;
	Word spr;

	Word dout;
	
	Word lnk;
	logic lnk_we;
	Word ctr;
	logic ctr_we;
	//logic jump;

	Msr msr;

	// read in WB
	//Word wb_res;
	//logic wb_cout;
	Cr_field wb_cr;

	Word wb_lnk;
	logic wb_lnk_we;
	Word wb_ctr;
	logic wb_ctr_we;
	//logic wb_jump;
	
	Word wb_spr;

	// -- internal --
	Word lnk_d;

	always_ff @(posedge clk or posedge reset)
	begin : delay
		if( reset ) begin
			lnk_d <= '0;
			wb_lnk <= '0;
			wb_lnk_we <= 1'b0;
            wb_ctr <= '0;
			wb_ctr_we <= 1'b0;
			wb_spr <= '0;
     //       wb_jump <= '0;
			//wb_res <= '0;
			//wb_cout <= '0;
			//wb_cr <= '0;
		end else begin
			lnk_d <= lnk;
			wb_lnk <= lnk_d;
			wb_lnk_we <= lnk_we;
			wb_ctr <= ctr;
			wb_ctr_we <= ctr_we;
			wb_spr <= spr;
	//		wb_jump <= jump;
			//wb_res <= res;
			//wb_cout <= cout;
			//wb_cr <= cr;
		end
	end : delay

	assign wb_cr = cr;
	
	//
	// modports
	//
	
	modport decode
		(	output lnk );

	modport alu
		(	output res,
			output cout,
			output cr,
			output spr,
			output msr );

	modport branch
		(	output ctr,
	//		output jump,
			output lnk_we, ctr_we );

	modport load_store
		(	output dout );

	modport write_back
		(	input res,
			input cout,
			input wb_cr,
			input wb_lnk,
			input wb_lnk_we,
			input wb_ctr_we,
			input wb_ctr,
	//		input wb_jump,
			input dout,
			input wb_spr,
			input msr );

	modport bypass(input res, dout);

endinterface
