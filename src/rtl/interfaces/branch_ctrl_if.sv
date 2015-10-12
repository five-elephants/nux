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

interface Branch_ctrl_if;
	logic en, en_decode, en_int;
	logic jump;
	logic dec_ctr;
	logic ctr_eq;     // corresponds to BO3
	logic[4:0] crbi;  // corresponds to BI
	logic cond;       // corresponds to BO1
	logic mask_ctr;   // corresponds to BO2
	logic mask_cond;  // corresponds to BO0
	logic save_link;  // store next instruction PC in LNK
	logic to_lnk;
	logic to_ctr;

	/*task automatic decode_set_zero;
		en_decode = '0;
		jump = '0;
		dec_ctr = '0;
		ctr_eq = '0;
		crbi = '0;
		cond = '0;
		mask_ctr = '0;
		mask_cond = '0;
		save_link = 1'b0;
		to_lnk = 1'b0;
		to_ctr = 1'b0;
	endtask*/

	assign en = en_decode & en_int;

	modport decode (
		//import decode_set_zero,
		output en_decode,
		output jump,
		output dec_ctr,
		output ctr_eq,
		output crbi,
		output cond,
		output mask_ctr,
		output mask_cond,
		output save_link,
		output to_lnk,
		output to_ctr );

	modport branch (
		input en,
		input jump,
		input dec_ctr,
		input ctr_eq,
		input crbi,
		input cond,
		input mask_ctr,
		input mask_cond,
		input save_link,
		input to_lnk,
		input to_ctr );

	modport int_sm ( output en_int );

endinterface
