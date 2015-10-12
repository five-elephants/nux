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

interface Timer_if();
	// read/write access on timer registers
	Timer      tbu, tbl;
	Timer      dec;
	Timer      decar;

	Timer      tbu_in, tbl_in;
	Timer      dec_in;
	Timer      decar_in;
	logic      tbu_we, tbl_we;
	logic      dec_we;
	logic      decar_we;

	// read/write for timer control register
	Tcr        tcr;
	Tcr        tcr_in;
	logic      tcr_we;

	// read/write for timer status register
	Tsr        tsr;
	Tsr        tsr_in;
	logic      tsr_we;


	// workaround for ncsim to access members of structs in interfaces...
	function automatic logic get_are();
		return tcr.are;
	endfunction


	modport timer (
		import get_are,
		output tbu, tbl, dec, decar, tcr, tsr,
		input tbu_in, tbl_in, dec_in, decar_in, tcr_in, tsr_in,
			tbu_we, tbl_we, dec_we, decar_we, tcr_we, tsr_we
	);

	modport pu (
		input tbu, tbl, dec, decar, tcr, tsr,
		output tbu_in, tbl_in, dec_in, decar_in, tcr_in, tsr_in,
			tbu_we, tbl_we, dec_we, decar_we, tcr_we, tsr_we
	);

	modport write_back (
		output tbu_in, tbl_in, dec_in, decar_in, tcr_in, tsr_in,
			tbu_we, tbl_we, dec_we, decar_we, tcr_we, tsr_we
	);

	modport op_fetch (
		input tbu, tbl, dec, decar, tcr, tsr
	);

	modport int_sched (
		input tcr, tsr
	);

	modport int_ctrl (
		input tcr, tsr
	);
endinterface
