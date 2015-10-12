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

interface Decode_ctrl_if();
	logic hold_data;
	logic hold_if;
	logic hold_ext;
	logic hold;

	assign hold = hold_data | hold_ext | hold_if;

	logic ready_ls;
	logic ready;

	assign ready = ready_ls;

	logic wakeup;

	modport decode(input hold, ready, wakeup);
	modport data_hazard_ctrl(output hold_data);
	modport ext_control(output hold_ext);
	modport inst_fetch(output hold_if);
	modport load_store(output ready_ls);
endinterface
