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

localparam int PROG_ADDR_WIDTH = 32;
localparam int SEL_BIT_SYSCTRL = 31;
localparam int SEL_BIT_ELEMS = 24;
localparam int SEL_BIT_MEMS = 16;
localparam int IOSEL_BIT_OUT = 29;
localparam int IOSEL_BIT_DEST = 14;

module Multiproc_top
	(	input logic clk,
		input logic resetb,

		output logic status_led,
		output logic[3:0] gpled,
		
		output logic sleep,
		//output logic[31:0] mon_pc,
		output logic heartbeat
	);

  //---------------------------------------------------------------------------
  // Local types and signals
  //---------------------------------------------------------------------------

  localparam int IMEM_ADDR_WIDTH = 13;
  localparam int DMEM_ADDR_WIDTH = 13;
  localparam int NUM_ELEMENTS = 6;

  logic sysclk;
  logic sysrst;

  logic[0:NUM_ELEMENTS-1] elem_resets;
  logic gpled_unconnected[4:5];

  //---------------------------------------------------------------------------
  // Local support logic
  //---------------------------------------------------------------------------

  Ram_if #(.ADDR_WIDTH(PROG_ADDR_WIDTH)) prog_sysctrl();

  /** Generate clock with half the input frequency.
  * Also synchronize resets and make sure reset is only set when PLL is locked. */
  clock_generator #(
    .MULTIPLICATOR(6),
    .DIVIDER(6),
    .CLK_PIN_PERIOD_NS(10.0)
  ) clkgen (
    .clk_pin(clk),
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

  System_control #(
    .NUM_ELEMENTS(NUM_ELEMENTS)
  ) sysctrl (
    .clk(sysclk),
    .reset(sysrst),
    .prog_if(prog_sysctrl),
    .elem_resets(elem_resets)
  );

  //---------------------------------------------------------------------------
  // Processing elements
  //---------------------------------------------------------------------------

  Ram_if #(PROG_ADDR_WIDTH, 32) prog_elems();

  Ram_if #(PROG_ADDR_WIDTH, 32) prog_el_0_if();
  Ram_if #(PROG_ADDR_WIDTH, 32) prog_el_1_if();
  Ram_if #(PROG_ADDR_WIDTH, 32) prog_el_2_if();

  Ram_if #(PROG_ADDR_WIDTH, 32) prog_el_3_if();
  Ram_if #(PROG_ADDR_WIDTH, 32) prog_el_4_if();
  Ram_if #(PROG_ADDR_WIDTH, 32) prog_el_5_if();

  Bus_if io_0(sysclk);
  Bus_if io_0_in(sysclk);
  Bus_if io_0_out(sysclk);
  Bus_if io_0_to_1_out(sysclk);
  Bus_if io_0_to_1_in(sysclk);
  Bus_if io_0_to_2_out(sysclk);
  Bus_if io_0_to_2_in(sysclk);

  Bus_if io_1(sysclk);
  Bus_if io_1_in(sysclk);
  Bus_if io_1_out(sysclk);
  Bus_if io_1_to_0_out(sysclk);
  Bus_if io_1_to_0_in(sysclk);
  Bus_if io_1_to_2_out(sysclk);
  Bus_if io_1_to_2_in(sysclk);

  Bus_if io_2(sysclk);
  Bus_if io_2_in(sysclk);
  Bus_if io_2_out(sysclk);
  Bus_if io_2_to_0_out(sysclk);
  Bus_if io_2_to_0_in(sysclk);
  Bus_if io_2_to_1_out(sysclk);
  Bus_if io_2_to_1_in(sysclk);

  Element #(
    .ID(0),
    .IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH),
    .DMEM_ADDR_WIDTH(DMEM_ADDR_WIDTH)
    `ifndef SYNTHESIS
      ,
      .SIM_CODE_IMG("test/testcode/neuroproc/synarray_code.raw"),
      .SIM_DATA_IMG("test/testcode/c/multiproc_demo_master_data.raw")
    `endif /* SYNTHESIS */
  ) el_0 (
    .clk(sysclk), 
    .reset(sysrst),
    .core_reset(elem_resets[0]),
    .prog(prog_el_0_if),
    .status_led(gpled[0]),
    .iobus(io_0)
  );

  Bus_if_split #(IOSEL_BIT_OUT) io_split_0 (
    .top(io_0),
    .out_0(io_0_in),
    .out_1(io_0_out)
  );

  Bus_if_split #(IOSEL_BIT_DEST) io_split_0_out (
    .top(io_0_out),
    .out_0(io_0_to_1_out),
    .out_1(io_0_to_2_out)
  );

  Bus_if_split #(IOSEL_BIT_DEST) io_split_0_in (
    .top(io_0_in),
    .out_0(io_1_to_0_in),
    .out_1(io_2_to_0_in)
  );

  Msg_queue q_01 (
    .writer(io_0_to_1_out),
    .reader(io_0_to_1_in)
  );

  Msg_queue q_02 (
    .writer(io_0_to_2_out),
    .reader(io_0_to_2_in)
  );

  Element #(
    .ID(1),
    .IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH),
    .DMEM_ADDR_WIDTH(DMEM_ADDR_WIDTH)
    `ifndef SYNTHESIS
      ,
      .SIM_CODE_IMG("test/testcode/neuroproc/neuron_code.raw"),
      .SIM_DATA_IMG("test/testcode/c/multiproc_demo_slave_data.raw")
    `endif  /* SYNTHESIS */
  ) el_1 (
    .clk(sysclk),
    .reset(sysrst),
    .core_reset(elem_resets[1]),
    .prog(prog_el_1_if),
    .status_led(gpled[1]),
    .iobus(io_1)
  );

  Bus_if_split #(IOSEL_BIT_OUT) io_split_1 (
    .top(io_1),
    .out_0(io_1_in),
    .out_1(io_1_out)
  );

  Bus_if_split #(IOSEL_BIT_DEST) io_split_1_out (
    .top(io_1_out),
    .out_0(io_1_to_0_out),
    .out_1(io_1_to_2_out)
  );

  Bus_if_split #(IOSEL_BIT_DEST) io_split_1_in (
    .top(io_1_in),
    .out_0(io_0_to_1_in),
    .out_1(io_2_to_1_in)
  );

  Msg_queue q_10 (
    .writer(io_1_to_0_out),
    .reader(io_1_to_0_in)
  );

  Msg_queue q_12 (
    .writer(io_1_to_2_out),
    .reader(io_1_to_2_in)
  );

  Element #(
    .ID(2),
    .IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH),
    .DMEM_ADDR_WIDTH(DMEM_ADDR_WIDTH)
    `ifndef SYNTHESIS
      ,
      .SIM_CODE_IMG("test/testcode/c/multiproc_demo_slave_code.raw"),
      .SIM_DATA_IMG("test/testcode/c/multiproc_demo_slave_data.raw")
    `endif  /* SYNTHESIS */
  ) el_2 (
    .clk(sysclk),
    .reset(sysrst),
    .core_reset(elem_resets[2]),
    .prog(prog_el_2_if),
    .status_led(gpled[2]),
    .iobus(io_2)
  );

  Bus_if_split #(IOSEL_BIT_OUT) io_split_2 (
    .top(io_2),
    .out_0(io_2_in),
    .out_1(io_2_out)
  );

  Bus_if_split #(IOSEL_BIT_DEST) io_split_2_out (
    .top(io_2_out),
    .out_0(io_2_to_0_out),
    .out_1(io_2_to_1_out)
  );

  Bus_if_split #(IOSEL_BIT_DEST) io_split_2_in (
    .top(io_2_in),
    .out_0(io_0_to_2_in),
    .out_1(io_1_to_2_in)
  );

  Msg_queue q_20 (
    .writer(io_2_to_0_out),
    .reader(io_2_to_0_in)
  );

  Msg_queue q_21 (
    .writer(io_2_to_1_out),
    .reader(io_2_to_1_in)
  );

  //---------------------------------------------------------------------------

  //Bus_if io_3(sysclk);
  //Bus_if io_3_in(sysclk);
  //Bus_if io_3_out(sysclk);
  //Bus_if io_3_to_4_out(sysclk);
  //Bus_if io_3_to_4_in(sysclk);
  //Bus_if io_3_to_5_out(sysclk);
  //Bus_if io_3_to_5_in(sysclk);

  //Bus_if io_4(sysclk);
  //Bus_if io_4_in(sysclk);
  //Bus_if io_4_out(sysclk);
  //Bus_if io_4_to_3_out(sysclk);
  //Bus_if io_4_to_3_in(sysclk);
  //Bus_if io_4_to_5_out(sysclk);
  //Bus_if io_4_to_5_in(sysclk);

  //Bus_if io_5(sysclk);
  //Bus_if io_5_in(sysclk);
  //Bus_if io_5_out(sysclk);
  //Bus_if io_5_to_3_out(sysclk);
  //Bus_if io_5_to_3_in(sysclk);
  //Bus_if io_5_to_4_out(sysclk);
  //Bus_if io_5_to_4_in(sysclk);

  //Element #(
    //.ID(3),
    //.IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH),
    //.DMEM_ADDR_WIDTH(DMEM_ADDR_WIDTH)
    //`ifndef SYNTHESIS
      //,
      //.SIM_CODE_IMG("test/testcode/c/multiproc_demo_master_code.raw"),
      //.SIM_DATA_IMG("test/testcode/c/multiproc_demo_master_data.raw")
    //`endif [> SYNTHESIS <]
  //) el_3 (
    //.clk(sysclk), 
    //.reset(sysrst),
    //.core_reset(elem_resets[3]),
    //.prog(prog_el_3_if),
    //.status_led(gpled[3]),
    //.iobus(io_3)
  //);

  //Bus_if_split #(IOSEL_BIT_OUT) io_split_3 (
    //.top(io_3),
    //.out_0(io_3_in),
    //.out_1(io_3_out)
  //);

  //Bus_if_split #(IOSEL_BIT_DEST) io_split_3_out (
    //.top(io_3_out),
    //.out_0(io_3_to_4_out),
    //.out_1(io_3_to_5_out)
  //);

  //Bus_if_split #(IOSEL_BIT_DEST) io_split_3_in (
    //.top(io_3_in),
    //.out_0(io_4_to_3_in),
    //.out_1(io_5_to_3_in)
  //);

  //Msg_queue q_34 (
    //.writer(io_3_to_4_out),
    //.reader(io_3_to_4_in)
  //);

  //Msg_queue q_35 (
    //.writer(io_3_to_5_out),
    //.reader(io_3_to_5_in)
  //);

  //Element #(
    //.ID(4),
    //.IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH),
    //.DMEM_ADDR_WIDTH(DMEM_ADDR_WIDTH)
    //`ifndef SYNTHESIS
      //,
      //.SIM_CODE_IMG("test/testcode/c/multiproc_demo_slave_code.raw"),
      //.SIM_DATA_IMG("test/testcode/c/multiproc_demo_slave_data.raw")
    //`endif  [> SYNTHESIS <]
  //) el_4 (
    //.clk(sysclk),
    //.reset(sysrst),
    //.core_reset(elem_resets[4]),
    //.prog(prog_el_4_if),
    //.status_led(gpled_unconnected[4]),
    //.iobus(io_4)
  //);

  //Bus_if_split #(IOSEL_BIT_OUT) io_split_4 (
    //.top(io_4),
    //.out_0(io_4_in),
    //.out_1(io_4_out)
  //);

  //Bus_if_split #(IOSEL_BIT_DEST) io_split_4_out (
    //.top(io_4_out),
    //.out_0(io_4_to_3_out),
    //.out_1(io_4_to_5_out)
  //);

  //Bus_if_split #(IOSEL_BIT_DEST) io_split_4_in (
    //.top(io_4_in),
    //.out_0(io_3_to_4_in),
    //.out_1(io_5_to_4_in)
  //);

  //Msg_queue q_43 (
    //.writer(io_4_to_3_out),
    //.reader(io_4_to_3_in)
  //);

  //Msg_queue q_45 (
    //.writer(io_4_to_5_out),
    //.reader(io_4_to_5_in)
  //);

  //Element #(
    //.ID(5),
    //.IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH),
    //.DMEM_ADDR_WIDTH(DMEM_ADDR_WIDTH)
    //`ifndef SYNTHESIS
      //,
      //.SIM_CODE_IMG("test/testcode/c/multiproc_demo_slave_code.raw"),
      //.SIM_DATA_IMG("test/testcode/c/multiproc_demo_slave_data.raw")
    //`endif  [> SYNTHESIS <]
  //) el_5 (
    //.clk(sysclk),
    //.reset(sysrst),
    //.core_reset(elem_resets[5]),
    //.prog(prog_el_5_if),
    //.status_led(gpled_unconnected[5]),
    //.iobus(io_5)
  //);

  //Bus_if_split #(IOSEL_BIT_OUT) io_split_5 (
    //.top(io_5),
    //.out_0(io_5_in),
    //.out_1(io_5_out)
  //);

  //Bus_if_split #(IOSEL_BIT_DEST) io_split_5_out (
    //.top(io_5_out),
    //.out_0(io_5_to_3_out),
    //.out_1(io_5_to_4_out)
  //);

  //Bus_if_split #(IOSEL_BIT_DEST) io_split_5_in (
    //.top(io_5_in),
    //.out_0(io_3_to_5_in),
    //.out_1(io_4_to_5_in)
  //);

  //Msg_queue q_53 (
    //.writer(io_5_to_3_out),
    //.reader(io_5_to_3_in)
  //);

  //Msg_queue q_54 (
    //.writer(io_5_to_4_out),
    //.reader(io_5_to_4_in)
  //);


  //---------------------------------------------------------------------------

  //---------------------------------------------------------------------------
  // JTAG access
  //---------------------------------------------------------------------------

  Jtag_if jtag_if();
  Ram_if #(.ADDR_WIDTH(PROG_ADDR_WIDTH)) prog_if();
  
  Jtag_v5 #(.CHAIN(1)) jtag_scan(jtag_if);
  Jtag_to_mem #(
    .NUM_SYNC_STAGES(2),
    .ADDR_WIDTH(PROG_ADDR_WIDTH),
    .DATA_WIDTH(32)
  ) jtag_to_mem (
    .clk(sysclk),
    .reset(sysrst),
    .mem(prog_if),
    .jtag(jtag_if)
  );

  Ram_if_split #(
    .SELECT_BIT(SEL_BIT_SYSCTRL)
  ) split_sysctrl (
    .clk(sysclk),
    .top(prog_if),
    .out_0(prog_elems),
    .out_1(prog_sysctrl)
  );

  // Element programming bus tree

  Ram_if #(PROG_ADDR_WIDTH, 32) prog_elems_2A();
  Ram_if #(PROG_ADDR_WIDTH, 32) prog_elems_2B();
  Ram_if #(PROG_ADDR_WIDTH, 32) prog_elems_1A();
  Ram_if #(PROG_ADDR_WIDTH, 32) prog_elems_1B();
  

  // *** Level 2 ***

  Ram_if_split #(
    .SELECT_BIT(SEL_BIT_ELEMS+2)
  ) split_elems_2A (
    .clk(sysclk),
    .top(prog_elems), 
    .out_0(prog_elems_2A), 
    .out_1(prog_elems_2B)
  );

  // *** Leve 1 ***


  Ram_if_split #(
    .SELECT_BIT(SEL_BIT_ELEMS+1)
  ) split_elems_1A (
    .clk(sysclk),
    .top(prog_elems_2A), 
    .out_0(prog_elems_1A), 
    .out_1(prog_elems_1B)
  );

  // *** Level 0 ***

  Ram_if_split #(
    .SELECT_BIT(SEL_BIT_ELEMS)
  ) split_elems_1B (
    .clk(sysclk),
    .top(prog_elems_2B), 
    .out_0(prog_el_4_if), 
    .out_1(prog_el_5_if)
  );

  Ram_if_split #(
    .SELECT_BIT(SEL_BIT_ELEMS)
  ) split_elems_0B (
    .clk(sysclk),
    .top(prog_elems_1B), 
    .out_0(prog_el_2_if), 
    .out_1(prog_el_3_if)
  );

  Ram_if_split #(
    .SELECT_BIT(SEL_BIT_ELEMS)
  ) split_elems_0A (
    .clk(sysclk),
    .top(prog_elems_1A), 
    .out_0(prog_el_0_if), 
    .out_1(prog_el_1_if)
  );

endmodule





/** One processing element with processor and memory */
module Element
  #(parameter int ID = 0,
    parameter int IMEM_JTAG_CHAIN = 2,
    parameter int DMEM_JTAG_CHAIN = 1,
    parameter int IMEM_ADDR_WIDTH = 13,
    parameter int DMEM_ADDR_WIDTH = 13
    `ifndef SYNTHESIS
      ,
      parameter string SIM_CODE_IMG= "test/testcode/c/eblinker_code.raw",
      parameter string SIM_DATA_IMG= "test/testcode/c/eblinker_data.raw"
    `endif  /* SYNTHESIS */  
    )
  ( input logic clk, reset,
    input logic core_reset,
    Ram_if.client prog,
    output logic status_led,
    Bus_if.master iobus);

  localparam IMEM_SIZE = 2**IMEM_ADDR_WIDTH;
  localparam DMEM_SIZE = 2**DMEM_ADDR_WIDTH;

  logic pu_hold;
  Word  pu_gout, pu_gin;

  //---------------------------------------------------------------------------
  // Core processor unit
  //---------------------------------------------------------------------------

  Pu_ctrl_if pu_ctrl();
  Timer_if   timer_if();
  Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_if();
  Ram_if #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_if();
  Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_prog_if();
  Ram_if #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_prog_if();
  Bus_if dmem_bus_if(.Clk(clk));  // only a dummy
  
  L1_memory_v5 #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem 
    (	.clk(clk),
      .reset(reset),
      .intf(imem_if),
      .intf2(imem_prog_if));

  L1_memory_v5 #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem
    (	.clk(clk),
      .reset(reset),
      .intf(dmem_if),
      .intf2(dmem_prog_if));

  Pu_v2 #(
    .OPT_BCACHE(3),
    .OPT_MULTIPLIER(1'b1),
    .OPT_DIVIDER(1'b1),
    .OPT_IOBUS(1'b1),
    .OPT_DMEM(MEM_TIGHT),
    .OPT_IF_LATENCY(1)
    )
    pcore
    (
    .clk(clk),
    .reset(reset | core_reset),
    .hold(pu_hold),
    .imem(imem_if),
    .dmem(dmem_if),
    .dmem_bus(dmem_bus_if),
    .iobus(iobus),
    .gout(pu_gout),
    .gin(pu_gin),
    .goe(),

    .ctrl(pu_ctrl),
    .timer(timer_if.pu)
  );

  assign status_led = pu_gout[0];
  assign pu_gin = '0;

  //---------------------------------------------------------------------------
  // Peripheral stuff
  //---------------------------------------------------------------------------

  Interrupt_ctrl interrupt_ctrl (
    .clk(clk),
    .reset(reset),
    .pu_ctrl(pu_ctrl.ctrl),
    //.ctrl(intf),
    .doorbell(1'b0),
    .timer(timer_if.int_ctrl),
    .en_clk(),
    .gin(32'b0)
  );

  Timer_unit timer (
    .clk(clk), .reset(reset),
    .intf(timer_if)
  );

  //---------------------------------------------------------------------------
  // JTAG programming interface
  //---------------------------------------------------------------------------

  Ram_if_split #(
    .SELECT_BIT(SEL_BIT_MEMS)
  ) split (
    .clk(clk),
    .top(prog),
    .out_0(imem_prog_if),
    .out_1(dmem_prog_if)
  );

  //Jtag_if jtag_dmem_if();
  //Jtag_if jtag_imem_if();
  ////Jtag_v5 #(.CHAIN((2*ID)+1)) jtag_dmem_scan(jtag_dmem_if);
  ////Jtag_v5 #(.CHAIN((2*ID)+2)) jtag_imem_scan(jtag_imem_if);
  //Jtag_v5 #(.CHAIN(DMEM_JTAG_CHAIN)) jtag_dmem_scan(jtag_dmem_if);
  //Jtag_v5 #(.CHAIN(IMEM_JTAG_CHAIN)) jtag_imem_scan(jtag_imem_if);

  //Jtag_to_mem #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) jtag_to_dmem
    //(	.clk(clk),
      //.reset(reset),
      //.mem(dmem_prog_if),
      //.jtag(jtag_dmem_if) );

  //Jtag_to_mem #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) jtag_to_imem
    //(	.clk(clk),
      //.reset(reset),
      //.mem(imem_prog_if),
      //.jtag(jtag_imem_if) );

  //---------------------------------------------------------------------------
  // Simulation code
  //---------------------------------------------------------------------------

  `ifndef SYNTHESIS
    initial begin
      Word imemimg[];
      Word dmemimg[];

      imemimg = new [IMEM_SIZE];
      dmemimg = new [DMEM_SIZE];

      Program_pkg::read_raw_image(SIM_CODE_IMG, imemimg);
      Program_pkg::read_raw_image(SIM_DATA_IMG, dmemimg);

      for(int i=0; i<IMEM_SIZE; i++)
        imem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[i] = imemimg[i];

      for(int i=0; i<DMEM_SIZE; i++)
        dmem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[i] = dmemimg[i];
    end
  `endif /** SYNTHESIS */
endmodule



/** System control registers accessible through ram_if */
module System_control
  #(parameter int NUM_ELEMENTS = 2)
  ( input logic clk, reset,
    Ram_if.memory prog_if,
  
    output logic[0:NUM_ELEMENTS-1] elem_resets);


  localparam int NUM_WIDTH = Pu_types::clog2(NUM_ELEMENTS);

  logic[NUM_WIDTH-1:0] el_sel;
  logic[0:NUM_ELEMENTS-1] elem_resets_i;

  assign el_sel = prog_if.addr[NUM_WIDTH-1:0];
  assign elem_resets = elem_resets_i;

  /** Write process */
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      elem_resets_i <= '1;
    end else begin
      if( prog_if.en && prog_if.we ) begin
        elem_resets_i[el_sel] <= prog_if.data_w[0];
      end
    end

  /** Read process */
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      prog_if.data_r <= '0;
    end else begin
      if( prog_if.en ) begin
        prog_if.data_r <= {31'b0, elem_resets_i[el_sel]};
      end
    end

  /** Unused signals */
  assign prog_if.delay = 1'b0;

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
