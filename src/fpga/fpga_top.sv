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

/** Toplevel module for the FPGA system */
module Fpga_top
	(	input logic clk,
		input logic resetb,

		output logic status_led,
		output logic[3:0] gpled,
		
		output logic sleep,
		//output logic[31:0] mon_pc,
		output logic heartbeat
	);

localparam IMEM_ADDR_WIDTH = 13;
localparam DMEM_ADDR_WIDTH = 13;
localparam IMEM_SIZE = 2**IMEM_ADDR_WIDTH;
localparam DMEM_SIZE = 2**DMEM_ADDR_WIDTH;

logic pu_hold;
logic core_reset;
Word  pu_gout, pu_gin;
logic ctrl_reg;
logic sysclk;
logic sysrst;


IBUFG clk_pin_ibufg (.I(clk), .O(clk_from_ibufg));

/** Generate clock with half the input frequency.
* Also synchronize resets and make sure reset is only set when PLL is locked. */
clock_generator #(
	.MULTIPLICATOR(10),
	.DIVIDER(9),
	//.MULTIPLICATOR(6),
	//.DIVIDER(12),
	.CLK_PIN_PERIOD_NS(10.0)
) clkgen (
  .clk_from_ibufg,
	.resetb_pin(resetb),
	.clk_out(sysclk),
	.reset_out(sysrst)
);


Heartbeat #(
	//.CYCLES_PER_SEC(100),
	//.PULSE_CYCLES(10)
	.CYCLES_PER_SEC(100000000),
	.PULSE_CYCLES  (20000000)
) heart (
	.clk(sysclk),
	.reset(sysrst),
	.led(heartbeat)
);

//---------------------------------------------------------------------------
Pu_ctrl_if pu_ctrl();
Timer_if   timer_if();
Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_if();
Ram_if #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_if();
Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_dma_if();
Ram_if #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_dma_if();
Bus_if iobus_if(.Clk(clk));
Bus_if dmem_bus_if(.Clk(clk));  // only a dummy
Syn_io_if syn_io_a_if(), syn_io_b_if();

L1_memory_v5 #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem 
	(	.clk(sysclk),
		.reset(sysrst),
		.intf(imem_if),
		.intf2(imem_dma_if));

L1_memory_v5 #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem
	(	.clk(sysclk),
		.reset(sysrst),
		.intf(dmem_if),
		.intf2(dmem_dma_if));

// load boot code image for simulation
// synthesis translate_off
//`include "__ram_boot_img.v"

initial begin
	Word imemimg[];
	Word dmemimg[];

	imemimg = new [IMEM_SIZE];
	dmemimg = new [DMEM_SIZE];

	//Program_pkg::read_raw_image("test/testcode/coremark_code.raw", imemimg);
	//Program_pkg::read_raw_image("test/testcode/coremark_data.raw", dmemimg);
	Program_pkg::read_raw_image("/afsuser/sfriedma/s2pp_testing/programs/coremark_tight_mem_single_iteration_code.raw", imemimg);
	Program_pkg::read_raw_image("/afsuser/sfriedma/s2pp_testing/programs/coremark_tight_mem_single_iteration_data.raw", dmemimg);

	for(int i=0; i<IMEM_SIZE; i++)
		imem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[i] = imemimg[i];

	for(int i=0; i<DMEM_SIZE; i++)
		dmem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[i] = dmemimg[i];

	//logic[7:0] dmemimg[0 : (4*DMEM_SIZE)-1];
	//$readmemh("test/testcode/c/eblinker_code.mem", imem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory);
	//$readmemh("test/testcode/c/eblinker_data.mem", dmemimg);
	//$readmemh("test/testcode/coremark_code", imem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory);
	//$readmemh("test/testcode/", dmemimg);

	//for(int i=0; i<DMEM_SIZE; i++) begin
		//dmem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[i] = { dmemimg[4*i], dmemimg[4*i+1], dmemimg[4*i+2], dmemimg[4*i+3] };
	//end
end
// synthesis translate_on


Pu_v2 #(
	.OPT_BCACHE(0),
	.OPT_MULTIPLIER(1'b1),
	.OPT_DIVIDER(1'b1),
	.OPT_NEVER(1'b0),
	.OPT_SYNAPSE(1'b0),
	.OPT_IOBUS(1'b0),
	.OPT_DMEM(MEM_TIGHT),
	.OPT_IF_LATENCY(1),
	.OPT_BCACHE_IGNORES_JUMPS(1'b1),
	.OPT_WRITE_THROUGH(1'b1),
	.OPT_LOOKUP_CACHE(1'b1)
	)
	pcore
	(
	.clk(sysclk),
	.reset(sysrst | core_reset),
	.hold(pu_hold),
	.imem(imem_if),
	.dmem(dmem_if),
	.dmem_bus(dmem_bus_if),
	.iobus(iobus_if),
	.gout(pu_gout),
	.gin(pu_gin),
	.goe(),

	.ctrl(pu_ctrl),
	.timer(timer_if.pu),
  .syn_io_a(syn_io_a_if),
  .syn_io_b(syn_io_b_if)
);

assign pu_hold = 1'b0;
assign pu_gin = 32'b0;
assign gpled = pu_gout[3:0];
assign status_led = ~sysrst & ~pu_hold & ~core_reset;

assign sleep = pu_ctrl.sleep;
//assign mon_pc = pu_ctrl.mon_pc;

Interrupt_ctrl interrupt_ctrl (
	.clk(sysclk),
	.reset(sysrst),
	.pu_ctrl(pu_ctrl.ctrl),
	//.ctrl(intf),
	.doorbell(1'b0),
	.timer(timer_if.int_ctrl),
	.en_clk(),
	.gin(32'b0)
);

Timer_unit timer (
	.clk(sysclk), .reset(sysrst),
	.intf(timer_if)
);

//---------------------------------------------------------------------------
// JTAG related modules
Jtag_if jtag_dmem_if();
Jtag_if jtag_imem_if();
Jtag_if jtag_ctrl_if();
Jtag_v5 #(.CHAIN(1)) jtag_dmem_scan(jtag_dmem_if);
Jtag_v5 #(.CHAIN(2)) jtag_imem_scan(jtag_imem_if);
Jtag_v5 #(.CHAIN(3)) jtag_ctrl_scan(jtag_ctrl_if);

Jtag_to_mem #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) jtag_to_dmem
	(	.clk(sysclk),
		.reset(sysrst),
		.mem(dmem_dma_if),
		.jtag(jtag_dmem_if) );

Jtag_to_mem #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) jtag_to_imem
	(	.clk(sysclk),
		.reset(sysrst),
		.mem(imem_dma_if),
		.jtag(jtag_imem_if) );

/** JTAG control chain
 *
 * at the moment 1 bit long to allow resetting of the processor core */
always_ff @(posedge jtag_ctrl_if.tck or posedge jtag_ctrl_if.treset or posedge sysrst)
begin
	if( jtag_ctrl_if.treset || sysrst ) begin
		ctrl_reg <= 1'b0;
	end else begin
		if( jtag_ctrl_if.sel ) begin
			if( jtag_ctrl_if.capture )
				ctrl_reg <= core_reset;

			if( jtag_ctrl_if.shift ) begin
				ctrl_reg <= jtag_ctrl_if.tdi;
			end
		end
	end
end

assign jtag_ctrl_if.tdo = ctrl_reg;

always_ff @(posedge sysclk or posedge sysrst )
begin
	if( sysrst ) 
		core_reset <= 1'b0;
	else begin
		if( jtag_ctrl_if.sel && jtag_ctrl_if.update )
			core_reset <= ctrl_reg;
	end
end

// synopsys translate_off
//---------------------------------------------------------------------------
// Embedded assertions
//---------------------------------------------------------------------------
//
/** Check resetting of processor core by JTAG */
property jtag_ctrl_hold;
	@(posedge jtag_ctrl_if.tck) disable iff(jtag_ctrl_if.treset)
	jtag_ctrl_if.sel == 1'b1 && jtag_ctrl_if.shift == 1'b1 
		&& jtag_ctrl_if.tdi == 1'b1
	|=> @(posedge sysclk)
	##[0:$] jtag_ctrl_if.update == 1'b1
	##1 core_reset == 1'b1;
endproperty

/** Check unsetting reset of processor core by JTAG */
property jtag_ctrl_unhold;
	@(posedge jtag_ctrl_if.tck) disable iff(jtag_ctrl_if.treset)
	jtag_ctrl_if.sel == 1'b1 && jtag_ctrl_if.shift == 1'b1 
		&& jtag_ctrl_if.tdi == 1'b0
	|=> @(posedge sysclk)
	##[0:$] jtag_ctrl_if.update == 1'b1
	##1 core_reset == 1'b0;
endproperty

check_jtag_hold: assert property(jtag_ctrl_hold);
cover_jtag_hold: cover property(jtag_ctrl_hold);

check_jtag_unhold: assert property(jtag_ctrl_unhold);
cover_jtag_unhold: cover property(jtag_ctrl_unhold);
//---------------------------------------------------------------------------
// synopsys translate_on


endmodule
