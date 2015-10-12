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

interface Load_store_ctrl_if;
	logic en, en_dec, en_int;
	logic dis_ex;
	logic en_dec_d;
	logic we;
	logic ls_we;

	/** Used together with load/store multiple */
	logic multiple, ls_multiple;
	logic first_cycle, ls_first_cycle;
	logic multiple_inc, ls_multiple_inc;
	
	Load_mode mode;
	Load_mode ls_mode;
	
	logic return_dout;
	logic keep_eff_addr;

	logic exts;  // extend sign for halfword operations

	logic is_update_op;
	logic do_request;

	//
	// processes
	//

	//always_ff @(posedge clk or posedge reset)
	//begin : delay
		//if( reset ) begin
			//ls_we <= '0;
			//ls_mode <= Load_word;
			//ls_multiple <= 1'b0;
			//ls_first_cycle <= 1'b0;
			//ls_multiple_inc <= 1'b0;
			//en_dec_d <= 1'b0;
		//end else begin
			//if( !dis_ex ) begin
				//ls_we <= we;
				//ls_mode <= mode;
				//ls_multiple <= multiple;
				//ls_first_cycle <= first_cycle;
				//ls_multiple_inc <= multiple_inc;
				//en_dec_d <= en_dec;
			//end else begin
				//ls_we <= 1'b0;
				//ls_mode <= Load_word;
				//ls_multiple <= 1'b0;
				//ls_first_cycle <= 1'b0;
				//ls_multiple_inc <= 1'b0;
				//en_dec_d <= 1'b0;
			//end
		//end
	//end : delay

	assign
		ls_we = we,
		ls_mode = mode,
		ls_multiple = multiple,
		ls_first_cycle = first_cycle,
		ls_multiple_inc = multiple_inc,
		en_dec_d = en_dec;

	//assign en = en_dec_d & en_int;
	assign en = en_dec;
	
	//
	// modports
	//

	modport decode
		(	//import decode_set_zero,
			output en_dec,
			output we, mode, multiple, first_cycle, multiple_inc,
			output return_dout, keep_eff_addr, exts, is_update_op, do_request );

	modport load_store 
		(	input en, ls_we, ls_mode, ls_multiple, ls_first_cycle, ls_multiple_inc, return_dout, keep_eff_addr, exts, is_update_op, do_request );

	modport int_sm ( output en_int, dis_ex );

endinterface


// vim: noexpandtab ts=4 sw=4 softtabstop=0 nosmarttab:
