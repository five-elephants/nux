// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef DIRECT_INSTRUCTION_LOADER_
`define DIRECT_INSTRUCTION_LOADER_

//---------------------------------------------------------------------------
class Direct_instruction_loader extends Instruction_loader;
	extern virtual function void load(input Instruction inst, State state);
	extern virtual function void load_state(input State state);
	extern virtual function State get_state();
	//extern virtual function void stop();
	//extern virtual function void start();
endclass
//---------------------------------------------------------------------------
function void
Direct_instruction_loader::load(input Instruction inst, State state);
	Word tmp;
	Inst tmp_inst;
	int sz;
	int tmp_pc;
	int unsigned tmp_iaddr;

	// load instruction
// 		imem_if.data_r <= inst.get();
	//uut.decode_data.inst <= inst.get();
	//uut.inst_fetch.decode_inst_i <= inst.get();
	//uut.imem.data_r <= inst.get();
	//uut.inst_fetch.inst <= inst.get();
	//tmp_inst = inst.get();
	//$force("uut/decode_data/inst", tmp_inst);
	//tmp_iaddr = unsigned'(state.get_pc()) % imem.MEM_SIZE;
	//$display("writing instruction to address %4h", tmp_iaddr);
	//imem.mem[tmp_iaddr] = inst.get();

	load_state(state);
endfunction

//---------------------------------------------------------------------------
function void
Direct_instruction_loader::load_state(input State state);
	Word tmp;
	int sz;
	int tmp_pc;
	int unsigned tmp_iaddr;

	// load PC
	//uut.decode_data.pc = state.get_pc();
	//uut.inst_fetch.iaddr = state.get_pc() + 2;
	//uut.inst_fetch.iaddr_reg = state.get_pc() + 1;
	//uut.decode_data.npc = state.get_pc() + 1;
	//uut.inst_fetch.iaddr = state.get_pc() -1;
	//tmp_pc = state.get_pc();
	//$signal_force("uut/inst_fetch/next_iaddr", tmp_pc, 0, 0[>freeze*/, 11ns/*cancel_period<]);
	//tmp_pc = tmp_pc + 1;
	//$signal_force("uut/inst_fetch/next_iaddr", tmp_pc, 12ns, 0[>deposit*/, 19ns/*cancel_period<]);

	// load GPRs
	for(int i=0; i<32; i++) begin
		uut.gpr_file.gpr[i] <= state.get_gpr(i);
	end

	// load CR
	for(int i=0; i<8; i++)
		uut.write_back.cr[i] <= state.get_cr(i);

	// load LNK
	uut.write_back.lnk <= state.get_lnk();

	// load CTR
	uut.write_back.ctr <= state.get_ctr();

	// load XER
	tmp = state.get_xer();
	uut.write_back.xer <= tmp[31:29];

	// load other SPRs
	uut.write_back.srr0 <= state.get_srr0();
	uut.write_back.srr1 <= state.get_srr1();
	uut.write_back.csrr0 <= state.get_csrr0();
	uut.write_back.csrr1 <= state.get_csrr1();
	uut.write_back.mcsrr0 <= state.get_mcsrr0();
	uut.write_back.mcsrr1 <= state.get_mcsrr1();
	uut.write_back.esr <= state.get_esr();
	uut.write_back.msr <= state.get_msr();
	uut.write_back.dear <= state.get_dear();

	// load gout
	uut.write_back.gout <= state.get_gout();
	uut.write_back.goe <= state.get_goe();

	// load memory
	sz = dmem.MEM_SIZE;

	for(Address i=0; i<sz; i++)
		dmem.mem[i] = state.get_mem(i);

	if( uut.OPT_NEVER == 1'b1 ) begin
		uut.gen_fub_never.fub_never.select_state = state.get_nve_sstate();
		for(int i=0; i<NUM_NVE_LUT; i++)
			uut.gen_fub_never.fub_never.lut[i] = state.get_nve_lut(i);
	end
endfunction
//---------------------------------------------------------------------------

function State
Direct_instruction_loader::get_state();
	Fixed_state s = new();
	Word xer;

	// load PC
	s.set_pc(pu_ctrl_if.mon_pc);

	// load GPRs
	for(int i=0; i<32; i++) begin
		s.set_gpr(i, uut.gpr_file.gpr[i]);
	end

	// load CR
	for(int i=0; i<8; i++)
		s.set_cr(i, uut.write_back.cr[i]);

	// load LNK
	s.set_lnk(uut.write_back.lnk);

	// load CTR
	s.set_ctr(uut.write_back.ctr);

	// load XER
	xer[31:29] = uut.write_back.xer;
	xer[28:0] = '0;
	s.set_xer(xer);

	// get other SPRs
	s.set_srr0(uut.write_back.srr0);
	s.set_srr1(uut.write_back.srr1);
	s.set_csrr0(uut.write_back.csrr0);
	s.set_csrr1(uut.write_back.csrr1);
	s.set_mcsrr0(uut.write_back.mcsrr0);
	s.set_mcsrr1(uut.write_back.mcsrr1);
	s.set_esr(uut.write_back.esr);
	s.set_msr(uut.write_back.msr);
	s.set_dear(uut.write_back.dear);

	// load gout
	s.set_gout(uut.write_back.gout);
	s.set_goe(uut.write_back.goe);

	// get mem
	for(Address i=0; i<dmem.MEM_SIZE; ++i)
		s.set_mem(i, dmem.mem[i]);

	if( uut.OPT_NEVER == 1'b1 ) begin
		s.set_nve_sstate(uut.gen_fub_never.fub_never.select_state);
		for(int i=0; i<NUM_NVE_LUT; i++)
			s.set_nve_lut(i, uut.gen_fub_never.fub_never.lut[i]);
	end

	return s;
endfunction

/*function void
Direct_instruction_loader::start();
	pu_hold <= 1'b0;
endfunction

function void
Direct_instruction_loader::stop();
	pu_hold <= 1'b1;
endfunction*/
//---------------------------------------------------------------------------

`endif
