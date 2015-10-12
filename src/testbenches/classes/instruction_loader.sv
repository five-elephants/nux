// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef INSTRUCTION_LOADER__
`define INSTRUCTION_LOADER__

`include "instruction.sv"
`include "state.sv"

virtual class Instruction_loader;
	pure virtual function void load(input Instruction inst, State state);
	pure virtual function State get_state();
endclass

`endif
