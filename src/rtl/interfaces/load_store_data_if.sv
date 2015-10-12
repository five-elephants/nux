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

interface Load_store_data_if
	(	input Address address,
		input Word din );

	Word dout;

	Word ls_din;

	Word bp_din;

	assign ls_din = din;
	assign bp_din = ls_din;

	//modport decode
		//(	output din );

	//modport alu
		//(	output address );

	modport load_store
		(	input address,
			input bp_din );

	modport bypass(input ls_din, output bp_din);

endinterface

// vim: noexpandtab ts=4 sw=4 softtabstop=0 nosmarttab:
