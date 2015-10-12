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

interface Gpr_file_if();
	Reg_index    ra_sel;
	Word         ra;

	Reg_index    rb_sel;
	Word         rb;

	Reg_index    rc_sel;
	Word         rc;

	Reg_index    wa_sel;
	logic        wa_wr;
	Word         wa;

	Reg_index    wb_sel;
	logic        wb_wr;
	Word         wb;


	modport processor (
		input ra, rb, rc,
		output ra_sel, rb_sel, rc_sel, wa_sel, wb_sel, wa, wb,
		output wa_wr, wb_wr
	);

	modport gpr_file (
		output ra, rb, rc,
		input ra_sel, rb_sel, rc_sel, wa_sel, wb_sel, wa, wb,
		input wa_wr, wb_wr
	);
endinterface
