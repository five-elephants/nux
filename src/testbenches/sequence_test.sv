// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



`ifndef PROGRAM_LENGTH
	`define PROGRAM_LENGTH 2
`endif

`ifndef OPT_BCACHE
	`define OPT_BCACHE 0
`endif


// `define USE_CACHE 1'b0
// `define OPT_DMEM_BUS


module Sequence_test
	#(	parameter int IMEM_ADDR_WIDTH = 10,
		parameter int DMEM_ADDR_WIDTH = 10,
		parameter int ICACHE_ADDR_WIDTH = 6,
		parameter int ICACHE_DISPLACEMENT = 4,
		parameter int OPT_VECTOR_SLICES = 2); 

timeunit 1ns;

import Pu_types::*;
import Pu_inst::*;
import Sit::*;

const time clk_period = 10ns;
logic clk;
logic reset;
logic pu_hold;
Word gout, gin, goe;
bit test_failed;

always begin
	clk = 0;
	#(clk_period/2) clk = 1;
	#(clk_period/2);
end

Pu_ctrl_if pu_ctrl_if();
Timer_if timer_if();

Bus_if iobus_if(.Clk(clk));
Bus_if #(.byteen(1'b1)) dmem_bus_if(.Clk(clk)),
    vector_bus_if(.Clk(clk)),
    memory_bus_if(.Clk(clk)); 
Bus_if #(.byteen(1'b1), .data_width(OPT_VECTOR_SLICES*128)) vector_pbus_if(.Clk(clk));

Iobus_dummy #(
	.RD_ACCEPT_LATENCY(0),
	.WR_ACCEPT_LATENCY(0),
	.RD_RETURN_LATENCY(1),
	.WR_RETURN_LATENCY(1),
	.RESPONSE_FUNCTION(2)  // 2 - return static 0
) iobus_dummy (
	.clk, .reset,
	.iobus(iobus_if)
);

Iobus_dummy #(
	.RD_ACCEPT_LATENCY(0),
	.WR_ACCEPT_LATENCY(0),
	.RD_RETURN_LATENCY(1),
	.WR_RETURN_LATENCY(1),
	.DATA_WIDTH(128*8),
	.RESPONSE_FUNCTION(2)  // 2 - return static 0
) vector_pbus_dummy (
	.clk, .reset,
	.iobus(vector_pbus_if)
);

Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_if();
Ram_if #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_if();
Syn_io_if syn_io_a_if(), syn_io_b_if();

Sim_memory #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem 
	(	.clk(clk),
		.reset(reset),
		.intf(imem_if) );

Sim_memory #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem
	(	.clk(clk),
		.reset(reset),
		.intf(dmem_if) );

`ifdef OPT_DMEM_BUS
	Bus_if_arb #(
		.RESET_BY_0(1)
	) memory_arb (
		.in_0(dmem_bus_if),
		.in_1(vector_bus_if),
		.out(memory_bus_if)
	);

	Bridge_bus2ram bus2ram(memory_bus_if, dmem_if);
`endif  /* OPT_DMEM_BUS */

//Iobus_dummy #(
	//.RESPONSE_FUNCTION(1),
	//.DATA_WIDTH(32),
	//.ADDR_WIDTH(32),
	//.BYTE_ENABLED(1'b1),
	//.MEM_DEFAULT('0)
//) bus_dmem (
	//.clk,
	//.reset,
	//.iobus(dmem_bus_if)
//);



`ifdef USE_CACHE	
	Bus_if #(.byteen(1'b1)) imem_bus_if(.Clk(clk));
	Ram_if #(.ADDR_WIDTH(ICACHE_ADDR_WIDTH)) cache_store_r_if(), cache_store_w_if();
	Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_cache_if();

	Pu_v2 #(
		.OPT_BCACHE(`OPT_BCACHE),

		.OPT_MULTIPLIER(1'b1),
		.OPT_DIVIDER(1'b1),
		.OPT_IOBUS(1'b1),
		.OPT_NEVER(1'b1),
		.OPT_SYNAPSE(1'b1),
		.OPT_VECTOR(1'b1),
		.OPT_VECTOR_SLICES(OPT_VECTOR_SLICES),
		.OPT_VECTOR_NUM_HALFWORDS(8),
		.OPT_VECTOR_MULT_DELAY(2),
		.OPT_VECTOR_ADD_DELAY(1),
		.OPT_VECTOR_INST_QUEUE_DEPTH(4),
		.OPT_BCACHE_IGNORES_JUMPS(1'b1),
		.OPT_BUFFER_BCTRL(1'b1),
		.OPT_WRITE_THROUGH(1'b1),
		.OPT_LOOKUP_CACHE(1'b1),
`ifdef OPT_DMEM_BUS
		.OPT_DMEM(MEM_BUS),
`else
		.OPT_DMEM(MEM_TIGHT),
`endif
		.OPT_IF_LATENCY(1) 
	) uut(
		.clk(clk),
		.reset(reset),
		.hold(pu_hold),
		.imem(imem_cache_if),
		.dmem(dmem_if),
		.dmem_bus(dmem_bus_if),
		.iobus(iobus_if),
    .vector_bus(vector_bus_if),
    .vector_pbus(vector_pbus_if),
		.gout(gout),
		.gin(gin),
		.goe(goe),
		.ctrl(pu_ctrl_if),
		.timer(timer_if),
		.syn_io_a(syn_io_a_if),
		.syn_io_b(syn_io_b_if)
	);

	Read_cache #(
	  .INDEX_SIZE(ICACHE_ADDR_WIDTH-ICACHE_DISPLACEMENT),
	  .DISPLACEMENT_SIZE(ICACHE_DISPLACEMENT),
	  .TAG_SIZE(IMEM_ADDR_WIDTH-ICACHE_ADDR_WIDTH),
	  .WORD_SIZE(32)
	) inst_cache (
	  .clk,
	  .reset,
	  .fetch_bus(imem_bus_if),
	  .read_bus(imem_cache_if),
	  .store_r(cache_store_r_if),
	  .store_w(cache_store_w_if)
	);

	Bridge_bus2ram bridge_imem(imem_bus_if, imem_if);

	L1_memory #(
		.ADDR_WIDTH(ICACHE_ADDR_WIDTH),
		.DATA_WIDTH(32),
		.IS_DUALPORT(1'b1)
	) cache_store (
		.clk,
		.reset,
		.intf(cache_store_r_if),
		.intf2(cache_store_w_if)
	);
`else
	Pu_v2 #(
		.OPT_BCACHE(`OPT_BCACHE),

		.OPT_MULTIPLIER(1'b1),
		.OPT_DIVIDER(1'b1),
		.OPT_IOBUS(1'b1),
		.OPT_NEVER(1'b1),
		.OPT_SYNAPSE(1'b1),
		.OPT_VECTOR(1'b1),
		.OPT_VECTOR_SLICES(2),
		.OPT_VECTOR_NUM_HALFWORDS(8),
		.OPT_VECTOR_MULT_DELAY(2),
		.OPT_VECTOR_ADD_DELAY(1),
		.OPT_VECTOR_INST_QUEUE_DEPTH(4),
		.OPT_BCACHE_IGNORES_JUMPS(1'b1),
		.OPT_BUFFER_BCTRL(1'b1),
		.OPT_WRITE_THROUGH(1'b1),
		.OPT_LOOKUP_CACHE(1'b1),

`ifdef OPT_DMEM_BUS
		.OPT_DMEM(MEM_BUS),
`else
		.OPT_DMEM(MEM_TIGHT),
`endif
		.OPT_IF_LATENCY(1) 
	) uut(
		.clk(clk),
		.reset(reset),
		.hold(pu_hold),
		.imem(imem_if),
		.dmem(dmem_if),
		.dmem_bus(dmem_bus_if),
		.iobus(iobus_if),
    .vector_bus(vector_bus_if),
    .vector_pbus(vector_pbus_if),
		.gout(gout),
		.gin(gin),
		.goe(goe),
		.ctrl(pu_ctrl_if),
		.timer(timer_if),
		.syn_io_a(syn_io_a_if),
		.syn_io_b(syn_io_b_if)
	);
`endif  /* USE_CACHE */

assign
	pu_ctrl_if.wakeup = 1'b0,
	pu_ctrl_if.doorbell = 1'b0,
	pu_ctrl_if.ext_input = 1'b0;

assign
	timer_if.tbu = '0,
	timer_if.tbl = '0,
	timer_if.dec = '0,
	timer_if.decar = '0,
	timer_if.tcr = '0,
	timer_if.tsr = '0;

`include "direct_instruction_loader.sv"

//---------------------------------------------------------------------------
// Random program generator class
//---------------------------------------------------------------------------
class Rand_program #(int image_size = 1024);
	typedef struct {
		int addr;
		Inst inst;
	} Program_line;

	const int length;
	Rand_instruction rinst;
	Sparse_mem_model memory;
	Static_mem_model io;
	Predictor predictor;
	Inst image[0:image_size-1];
	Program_line listing[];

	State istate;
	State fstate;

	extern function new(input int length);

	extern virtual function void set_init_state(const ref State state);
	extern virtual function void create_program();
	extern virtual function State get_final_state();
	
endclass
//---------------------------------------------------------------------------
function 
Rand_program::new(input int length);
	this.length = length;
	rinst = new(istate,
		._no_branches(1'b1),
		._no_wait(1'b1),
		._no_exceptions(1'b1),
		.addr_space_size(2**IMEM_ADDR_WIDTH));
	predictor = new();
	memory = new(2**DMEM_ADDR_WIDTH);
	io = new();

	for(int i=0; i<image_size; i++)
		image[i] = Pu_inst::INST_NOP;

	listing = new [length];
endfunction
//---------------------------------------------------------------------------
function automatic void
Rand_program::set_init_state(const ref State state);
	istate = state;
endfunction
//---------------------------------------------------------------------------
function automatic void
Rand_program::create_program();
	State intermed;

	intermed = istate;

	for(int i=0; i<length-1; i++) begin
		rinst.set_state(intermed);
		rinst.randomize();
		image[i] = rinst.get();

		intermed = predictor.predict(rinst, intermed);
		listing[i].addr = i;
		listing[i].inst = image[i];
	end

	image[length-1] = Pu_inst::INST_WAIT;
	listing[length-1].addr = length-1;
	listing[length-1].inst = Pu_inst::INST_WAIT;

	fstate = intermed;
endfunction
//---------------------------------------------------------------------------
function automatic State
Rand_program::get_final_state();
	return fstate;
endfunction
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Generate random programs containing branches
//---------------------------------------------------------------------------
class Rand_branching_program #(int image_size = 1024) extends Rand_program #(image_size);

	function new(input int length=1024);
		super.new(length);

		rinst = new(istate,
			._no_branches(1'b0),
			._no_wait(1'b1),
			._no_exceptions(1'b1),
			.addr_space_size(image_size/2));  // only use the upper half of the address space
			                                  // (first instruction jumps to addr_space_size-1 ...)
	endfunction

	virtual function void create_program();
		State intermed, next_intermed;
		int addr, next_addr;

		memory.clear(0);
		io.clear(0);

		// clear memory
		for(int i=0; i<image_size; i++)
			image[i] = Pu_inst::INST_NOP;

		intermed = istate;

		addr = 0;
		for(int i=0; i<length-1; i++) begin
			rinst.set_state(intermed);
			rinst.randomize();
			image[addr] = rinst.get();

			listing[i].addr = addr;
			listing[i].inst = image[addr];

			next_intermed = predictor.predict(rinst, intermed);
			
			next_addr = next_intermed.get_pc();
			assert((next_addr >= 0) && (next_addr < image_size));

			// No recurrent programs to avoid infinite loop problems
			while( image[next_addr] != Pu_inst::INST_NOP )
			begin
				rinst.randomize();
				image[addr] = rinst.get();
				next_intermed = predictor.predict(rinst, intermed);
				next_addr = next_intermed.get_pc();
				assert((next_addr >= 0) && (next_addr < image_size));
			end

			addr = next_addr;
			intermed = next_intermed;
		end

		image[addr] = Pu_inst::INST_WAIT;
		fstate = intermed;
		listing[length-1].addr = addr;
		listing[length-1].inst = Pu_inst::INST_WAIT;
	endfunction
endclass 
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Sequence testing program
//---------------------------------------------------------------------------
program rand_sequence_stim
	(	input logic clk,
		input Word gout,
		output logic reset, pu_hold,
		output Word gin );

	default clocking cb @(posedge clk);
		default input #1step output #4;
		output negedge reset;

		input #1step output #4 pu_hold;
		input #1step output #4 gin;
	endclocking


	// internal objects
	//Rand_program rprog;
	Rand_branching_program #(2**IMEM_ADDR_WIDTH) rprog;
	Direct_instruction_loader loader;
	Cmp_ignore_mask mask;
	Rand_state rand_state;
	
	initial begin
		Mem_model tmp_io;

		rprog = new(`PROGRAM_LENGTH);
		loader = new();
		tmp_io = rprog.io;

		rand_state = new(rprog.memory, tmp_io, 2**IMEM_ADDR_WIDTH, 2**32);

		test_failed = 0;

		//clk <= 1'b0;
		reset <= 1'b1;    // assignment to set it from time 0
		cb.reset <= 1'b1; // assignment through clocking block
		cb.pu_hold <= 1'b0;
		cb.gin <= '0;

		// set comparison mask for state comparison at end of program
		mask.pc = 1'b1;  // ignore PC changes (predictor does not predict this)
		for(int i=0; i<32; i++) mask.gpr[i] = 1'b0;
		for(int i=0; i<8; i++) mask.cr[i] = 1'b0;
		mask.ctr = 1'b0;
		mask.lnk = 1'b0;
		mask.xer = 1'b0;
		mask.gout = 1'b0;
		mask.mem = 1'b1;  // ignore data memory changes
		mask.io = 1'b0;

		// init instruction memory to nops
		for(int i=0; i<(2**IMEM_ADDR_WIDTH); i++) begin
			Inst nop;

			nop.d.opcd = Op_ori;
			nop.d.rt = '0;
			nop.d.ra = '0;
			nop.d.d = '0;

			imem.mem[i] <= nop;
		end

		// init data memory to zeros 
		// (bus based memory uses Iobus_dummy which returns 0 by default)
`ifndef OPT_DMEM_BUS
		for(int i=0; i<(2**DMEM_ADDR_WIDTH); i++)
			dmem.mem[i] <= '0;
`endif  /* OPT_DMEM_BUS */

		forever begin : loop_programs
			State istate;
			State fstate;
			State state;
			bit cmp_res;
			bit timeout;

			// hold reset
			cb.reset <= 1'b1;
			##3;

			// generate random program
			//istate = loader.get_state();

			rand_state.randomize();
			rand_state.pc = 0;
			istate = rand_state;
			loader.load_state(istate);
			rprog.set_init_state(istate);
			rprog.create_program();

			// transfer to memory
			foreach(rprog.image[i])
				imem.mem[i] = rprog.image[i];


			// run program
			/*##1*/ cb.reset <= 1'b0;

			//while( uut.decode_data.pc < `PROGRAM_LENGTH + 4
				//|| uut.decode_data.pc == 32'hffffffff ) ##1;

			timeout = 0;
			fork
				begin : timeout_proc
					##(`PROGRAM_LENGTH *100);
					timeout = 1;
					$display("program timed out");
				end

				begin : sleep_wait_proc
					@(pu_ctrl_if.sleep == 1'b1);
					disable timeout_proc;
				end
			join

			// compare endstate and prediction
			fstate = loader.get_state();

			cmp_res = compare_state_masked(rprog.get_final_state(), 
					fstate, mask);
			check_sequence_endstate: assert(cmp_res)
				else $error("mismatch");
			check_no_timeout: assert(timeout == 0)
				else $error("timeout");

			if( !cmp_res || timeout ) begin
				test_failed = 1;
				$display("--------------------------------------");
				$display("Program of length %d was:", rprog.length);
				for(int i=0; i<rprog.length; i++)
					$display("0x%08h : 0x%08h (RT:%02d, RA:%02d, RB:%02d, OPCD: %s, XO: %s)",
						rprog.listing[i].addr,
						rprog.listing[i].inst,
						rprog.listing[i].inst.x.rt,
						rprog.listing[i].inst.x.ra,
						rprog.listing[i].inst.x.rb,
						rprog.listing[i].inst.x.opcd,
						rprog.listing[i].inst.xo.xo);

				$display("--------------------------------------");
			end
		end : loop_programs
	end


	//---------------------------------------------------------------------------
	// Coverage analysis of sequences
	//---------------------------------------------------------------------------
	/*property raw_hazard;
		Reg_index rt, ra;

		@(posedge clk) disable iff(reset)
		( (uut.decode.reduce.reduced.write_gpr_from_alu, rt = uut.decode.reduce.reduced.gpr_from_alu)
		  ##[1:3] uut.decode.reduce.reduced.read_gpr_a
	endproperty*/
	//---------------------------------------------------------------------------
endprogram

rand_sequence_stim prog(.*);


//---------------------------------------------------------------------------
// Coverage
//---------------------------------------------------------------------------


//---------------------------------------------------------------------------
// Coverage of the instruction word
covergroup cg_inst @(posedge clk);
	coverpoint pu_ctrl_if.mon_inst iff(pu_hold == 1'b0) ;
endgroup

cg_inst cg_inst_inst = new();
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Coverage of opcodes
covergroup cg_opcd @(posedge clk);
	alu_xo: coverpoint pu_ctrl_if.mon_inst.d.opcd iff(reset == 1'b0) {
		bins xo = {Op_alu_xo};
		bins others[] = default;
	}

	bclr: coverpoint pu_ctrl_if.mon_inst.d.opcd iff(pu_hold == 1'b0) {
		bins bclr = {Op_bclr};
		bins others[] = default;
	}

	opcd: coverpoint pu_ctrl_if.mon_inst.d.opcd iff(reset == 1'b0) {
		ignore_bins null_op = { Op_null };
	}
	xo: coverpoint pu_ctrl_if.mon_inst.xo.xo iff(reset == 1'b0) {
		ignore_bins null_op = { Xop_xo_null };
	}
	x: coverpoint pu_ctrl_if.mon_inst.x.xo iff(reset == 1'b0);
	xl: coverpoint pu_ctrl_if.mon_inst.xl.xo iff(reset== 1'b0);
	xfx: coverpoint pu_ctrl_if.mon_inst.xfx.xo iff( reset == 1'b0) {
		ignore_bins null_op = { Xop_xfx_null };
	}

	alu_xo_form: cross alu_xo, xo;
	alu_x_form: cross alu_xo, x;
	branch_xl_form: cross bclr, xl;
	move_xfx_form: cross alu_xo, xfx;
endgroup

cg_opcd cg_opcd_inst = new();
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
endmodule


/* vim: set noet fenc= ff=unix sts=0 sw=2 ts=2 : */
