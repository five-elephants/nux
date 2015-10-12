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

/** Embedded system toplevel
*
* This is a more complex embedded system, featuring a s2pp micro-processor, an
* internal bus infrastructure and several peripheral components inside FPGA
* logic. The system is initially targetted at providing a test environment
* (JTAG master and clock generation) for the tc65nm test chip processor.
* Simultaneously the system mimics the HICANN logical structure and can be
* used to prove the necessary concepts (bus arbitration, ...) in the FPGA.
*
*
*  ===  CURRENT SETUP:  ===
*
* [JTAG/ETH/USB - input] --<Bus_if>-- |            |
*                                     | Bus_if_arb | --<Bus_if>-- |Bus_if   |
*                [Pu_v2] --<Bus_if>-- |            |              |splitting| 
*                                                                 |network  |
*                                                                     |
*                                                                     |
*                                    [global control registers] ------+
*                                                                     |
*                                    [frequency synthesis] -----------+
*                                                                     |
*                                    [JTAG master] -------------------+
*                                                                     |
*                                    [processor memory] --------------+
*
*
*  ===  ALTERNATIVE SETUP  ===
*
* [JTAG/ETH/USB - input] --<Bus_if>-- |            |
*                                     | Bus_if_arb | --<Bus_if>-- |Bus_if   |
*            [processor] --<Bus_if>-- |            |              |splitting| 
*                 |                                               |network  |
*                 |                                                   |
*                 |                                                   |
*                 |                  [global control registers] ------+
*                 |                                                   |
*                 |                  [frequency synthesis] -----------+
*                 |                                                   |
*                 |                  [JTAG master] -------------------+
*                 |                                                   |
*                 +----------------- | Bus_if_arb | ------------------+
*                                          |
*                                          |
*                                 [ processor memory ]
* */
module Emsys_top
  #(parameter bit USE_PROCESSOR = 1'b1,
    parameter int IMEM_ADDR_WIDTH = 13,
    parameter int ICACHE_ADDR_WIDTH = 10,
    parameter int ICACHE_DISPLACEMENT = 4)
  ( input logic clk_in,
    input logic resetb,

    // from slave point of view
    input logic sl_tdo,
    output logic sl_tdi,
    output logic sl_tms,
    output logic sl_tck,
    inout wire sl_gpio[3:0],

    output logic gen_clk,
    output logic feten,

    output logic status_led,
    output logic[3:0] gpled,
    output logic sleep,
    output logic heartbeat );

  //---------------------------------------------------------------------------
  // Local types & signals
  //---------------------------------------------------------------------------
  
  typedef Word Cregs_t[0:0];

  typedef struct packed {
    logic[31:1] dummy;
    logic       core_reset_b;
  } Creg_resets_t;

  logic clk, reset;
  logic core_reset;
  Word pu_gout, pu_gin, pu_goe;
  Cregs_t cregs;
  Creg_resets_t creg_resets; 

  assign creg_resets = Creg_resets_t'(cregs[0]);
  assign core_reset = ~creg_resets.core_reset_b; 


  //---------------------------------------------------------------------------
  // Clocking & reset
  //---------------------------------------------------------------------------

  /** Generate clock 
  * Also synchronize resets and make sure reset is only set when PLL is locked. */
  clock_generator #(
    .MULTIPLICATOR(8),
	//.DIVIDER(6),
	//.DIVIDER(12),
	.DIVIDER(16),
    .CLK_PIN_PERIOD_NS(10.0)
  ) clkgen (
    .clk_from_pin(clk_in),
    .resetb_pin(resetb),
    .clk_out(clk),
    .reset_out(reset)
  );

  Heartbeat #(
    //.CYCLES_PER_SEC(100),
    //.PULSE_CYCLES(10)
    .CYCLES_PER_SEC(100000000),
    .PULSE_CYCLES  ( 20000000)
  ) heart (
    .clk(clk),
    .reset(reset),
    .led(heartbeat)
  );

  //---------------------------------------------------------------------------
  // Connection to host PC & bus master arbitration
  //---------------------------------------------------------------------------
 
  Bus_if #(.byteen(1'b1)) bus_jtag_in(.Clk(clk));
  Bus_if #(.byteen(1'b1)) bus_proc(.Clk(clk));
  Bus_if #(.byteen(1'b1)) bus_master(.Clk(clk));
  Bus_if #(.byteen(1'b1)) bus_master_d(.Clk(clk));

  Jtag_input jtag_in(
    .reset,
    .bus(bus_jtag_in)
    //.bus(bus_master)
  );

  Bus_if_arb #(
    .RESET_BY_0(1'b1),
    .NUM_IN_FLIGHT(16)
  ) master_arb (
    .in_0(bus_jtag_in),
    .in_1(bus_proc),
    //.out(bus_master)
    .out(bus_master_d)
  );
 
  //Bus_slave_terminator terminate_bus_master(bus_master);

  //Bus_delay delay_master(
    //.in(bus_master),
    //.out(bus_master_d)
  //);



  //---------------------------------------------------------------------------
  // Bus splitting network to components
  //---------------------------------------------------------------------------
  
  Bus_if #(.byteen(1'b1)) bus_cregs(.Clk(clk));
  Bus_if #(.byteen(1'b1)) bus_freq_synth(.Clk(clk));
  Bus_if #(.byteen(1'b1)) bus_jtag(.Clk(clk));
  Bus_if #(.byteen(1'b1)) bus_proc_mem(.Clk(clk));

  /*
  *  <bus_master>--[bus_split_root]
  *                     |
  *                     +--<bus_split_0_if>--[bus_split_0]
  *                     |                           |
  *                     |                           +--<bus_proc_mem>
  *                     |                           +--<bus_cregs>
  *                     +--<bus_split_1_if>--[bus_split_1]
  *                                                 |
  *                                                 +--<bus_jtag>
  *                                                 +--<bus_freq_synth>
  *
  * ADDRESS MAP:
  *
  * 0x0000_0000    processor memory block (bus_proc_mem)
  * 0x1000_0000    control registers (bus_cregs)
  * 0x2000_0000    slave jtag controller (bus_jtag)
  * 0x3000_0000    frequency synthesis (bus_freq_synth)
  * */

  Bus_if #(.byteen(1'b1)) bus_split_0_if(.Clk(clk));
  Bus_if #(.byteen(1'b1)) bus_split_1_if(.Clk(clk));


  //Iobus_dummy #(
    //.RESPONSE_FUNCTION(1)  // return address
  //) mem2 (
    //.clk, .reset,
    //.iobus(bus_master_d)
  //);
  Bus_if_split #(
    .SELECT_BIT(29),
    .NUM_IN_FLIGHT(16)
  ) bus_split_root(
    .top(bus_master_d),
    .out_0(bus_split_0_if),
    .out_1(bus_split_1_if)
  );

  //Bus_slave_terminator terminate_split_0(bus_split_0_if);
  //Bus_slave_terminator terminate_split_1(bus_split_1_if);
  Bus_if_split #(
    .SELECT_BIT(28),
    .NUM_IN_FLIGHT(16)
  ) bus_split_0(
    .top(bus_split_0_if),
    .out_0(bus_proc_mem),
    .out_1(bus_cregs)
  );

  Bus_if_split #(
    .SELECT_BIT(28),
    .NUM_IN_FLIGHT(16)
  ) bus_split_1(
    .top(bus_split_1_if),
    .out_0(bus_jtag),
    .out_1(bus_freq_synth)
  );

  //---------------------------------------------------------------------------
  // Processor core instantiation
  //---------------------------------------------------------------------------

  generate if( USE_PROCESSOR ) begin : gen_proc
    localparam int CODE_SPACE_BEGIN = 32'h0000_0000/4;
    localparam int CODE_SPACE_END   = 32'h0000_2fb4/4;
    localparam int DATA_SPACE_BEGIN = 32'h0000_2fb8/4;
    localparam int DATA_SPACE_END   = 32'h0000_4454/4;

    Pu_ctrl_if pu_ctrl();
    Timer_if timer_if();
    Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_if();
    Bus_if #(.byteen(1'b1)) imem_bus_if(.Clk(clk));
    Ram_if dmem_dummy_if();
    Bus_if #(.byteen(1'b1)) dmem_bus_if(.Clk(clk));
    Bus_if #(.byteen(1'b1)) dmem_bus_if_dummy(.Clk(clk));
    Bus_if iobus_dummy(.Clk(clk));
    Ram_if #(.ADDR_WIDTH(ICACHE_ADDR_WIDTH)) cache_store_r_if();
    Ram_if #(.ADDR_WIDTH(ICACHE_ADDR_WIDTH)) cache_store_w_if();
    Syn_io_if syn_io_a_if(), syn_io_b_if();

    Pu_v2 #(
      .OPT_BCACHE(6),
      .OPT_MULTIPLIER(1'b1),
      .OPT_DIVIDER(1'b1),
      .OPT_IOBUS(1'b0),
      .OPT_NEVER(1'b0),
      .OPT_SYNAPSE(1'b0),
      .OPT_DMEM(MEM_BUS),
      .OPT_IF_LATENCY(1),
      .OPT_BCACHE_IGNORES_JUMPS(1'b1)
    ) pcore (
      .clk(clk),
      .reset(reset | core_reset),
      .hold(1'b0),
      .imem(imem_if),
      .dmem(dmem_dummy_if),
      .dmem_bus(dmem_bus_if),
      .iobus(iobus_dummy),
      .gout(pu_gout),
      .gin(pu_gin),
      .goe(pu_goe),
      .ctrl(pu_ctrl),
      .timer(timer_if.pu),
      .syn_io_a(syn_io_a_if),
      .syn_io_b(syn_io_b_if)
    );
   
    //Bridge_ram2bus_ro imem2bus (
      //.clk, .reset(reset | core_reset),
      //.ram(imem_if),
      //.bus(imem_bus_if)
      ////.bus(bus_proc)
    //);

    Read_cache #(
      .INDEX_SIZE(ICACHE_ADDR_WIDTH - ICACHE_DISPLACEMENT),
      .DISPLACEMENT_SIZE(ICACHE_DISPLACEMENT),
      .TAG_SIZE(IMEM_ADDR_WIDTH-ICACHE_ADDR_WIDTH),
      .WORD_SIZE(32)
    ) inst_cache (
      .clk,
      .reset(reset | core_reset),
      .fetch_bus(imem_bus_if),
      //.fetch_bus(bus_proc),
      .read_bus(imem_if),
      .store_r(cache_store_r_if),
      .store_w(cache_store_w_if)
    );

    L1_memory #(
      .ADDR_WIDTH(ICACHE_ADDR_WIDTH),
      .DATA_WIDTH(32),
      .IS_DUALPORT(1'b1)
    ) cache_store (
      .clk,
      .reset(reset | core_reset),
      .intf(cache_store_r_if),
      .intf2(cache_store_w_if)
    );

    //Bus_master_terminator terminate_dmem_bus(dmem_bus_if_dummy);

    Bus_if_arb #(
      .RESET_BY_0(1'b1),
      .NUM_IN_FLIGHT(16)
    ) imem_dmem_arb (
      .in_0(imem_bus_if),
      .in_1(dmem_bus_if),
      .out(bus_proc)
    );

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

    assign sleep = pu_ctrl.sleep;

    `ifndef SYNTHESIS
      check_dmem_bus_addr_range: assert property (
	@(posedge dmem_bus_if.Clk) disable iff(!dmem_bus_if.MReset_n)
	( (dmem_bus_if.MCmd != Bus::IDLE) |-> (unsigned'(dmem_bus_if.MAddr) < unsigned'(2**IMEM_ADDR_WIDTH)) )
      ) else
	$warning("processor requesting out-of-range addresses on the data bus (0x%08h)",
	  dmem_bus_if.MAddr);

      check_no_access_to_codespace: assert property (
	@(posedge dmem_bus_if.Clk) disable iff(!dmem_bus_if.MReset_n)
	( (dmem_bus_if.MCmd != Bus::IDLE)
	  |-> !((dmem_bus_if.MAddr >= CODE_SPACE_BEGIN) && (dmem_bus_if.MAddr <= CODE_SPACE_END)) )
      ) else
	$warning("processor accessing code space via load/store at address 0x%08h (space ranges from 0x%08h to 0x%08h)",
	  dmem_bus_if.MAddr, CODE_SPACE_BEGIN, CODE_SPACE_END);

      check_no_write_to_codespace_2: assert property (
	@(posedge bus_proc_mem.Clk) disable iff(!bus_proc_mem.MReset_n | core_reset)
	( (bus_proc_mem.MCmd == Bus::WR)
	  |-> !((bus_proc_mem.MAddr >= CODE_SPACE_BEGIN) && (bus_proc_mem.MAddr <= CODE_SPACE_END)) )
      ) else
	$warning("someone writing into code space at address 0x%08h during processor operation",
	  dmem_bus_if.MAddr);

      check_fetch_from_codespace: assert property (
	@(posedge dmem_bus_if.Clk) disable iff(!dmem_bus_if.MReset_n)
	( (imem_bus_if.MCmd == Bus::RD)
	  |-> ((imem_bus_if.MAddr >= CODE_SPACE_BEGIN) && (imem_bus_if.MAddr <= CODE_SPACE_END)) )
      ) else
	$warning("processor fetching instructions from outside of code space at address 0x%08h (code space ranges from 0x%08h to 0x%08h)",
	  dmem_bus_if.MAddr, CODE_SPACE_BEGIN, CODE_SPACE_END);

      check_stack_overflow: assert property (
	@(posedge clk) disable iff(reset | core_reset)
	( (pcore.gpr_file.gpr[1] > DATA_SPACE_END*4) && (pcore.gpr_file.gpr[1] < 2**IMEM_ADDR_WIDTH *4) )
      ) else
	$warning("Stack pointer out of range at 0x%08h (allowed: 0x%08h to 0x%08h)",
	  pcore.gpr_file.gpr[1], DATA_SPACE_END*4, 2**IMEM_ADDR_WIDTH *4 -1);

    `endif /** SYNTHESIS */
    

  end : gen_proc
  else
  begin : gen_no_proc
    
    Bus_master_terminator term_bus_proc(bus_proc);

    assign 
      sleep = 1'b1,
      pu_goe = '0,
      pu_gout = '0;

  end : gen_no_proc
  endgenerate
 

  //---------------------------------------------------------------------------
  // Processor memory block
  //---------------------------------------------------------------------------

  //Iobus_dummy #(
    //.RESPONSE_FUNCTION(1) 
  //) mem (
    //.clk, .reset,
    //.iobus(bus_proc_mem)
  //);
  Memory_block #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) proc_mem (
    .bus(bus_proc_mem)
  );

  `ifndef SYNTHESIS
    property cache_correctness;
      int addr;

      @(posedge clk) disable iff(reset || core_reset || !USE_PROCESSOR)
      ( (gen_proc.imem_if.en && !reset && !core_reset, addr=gen_proc.imem_if.addr)
        ##1 !gen_proc.imem_if.delay
        |-> (gen_proc.imem_if.data_r == proc_mem.mem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[addr]) );
    endproperty

    check_cache_correctnes: assert property (cache_correctness)
    else
      $error("cache delivering incorrect instructions");

    check_inst_stream: assert property (
      @(posedge clk) disable iff(reset || core_reset || !USE_PROCESSOR)
      ( (gen_proc.pcore.frontend.fst_d.inst == proc_mem.mem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[gen_proc.pcore.frontend.fst_d.pc])
        || (gen_proc.pcore.frontend.fst_d.inst == Pu_inst::INST_NOP)
        || (gen_proc.pcore.frontend.fst_d.inst == 0) )
    ) else
      $error("inst stream delivering incorrect instructions (PC: 0x%08h, fst_d: 0x%08h, expected: 0x%08h)",
        gen_proc.pcore.frontend.fst_d.pc, gen_proc.pcore.frontend.fst_d.inst,proc_mem.mem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[gen_proc.pcore.frontend.fst_d.pc]);

    //property cache_fetch_correctness;
      //int addr;
      //int data;
      //int exp;

      //@(posedge gen_proc.imem_bus_if.Clk) disable iff(!gen_proc.imem_bus_if.MReset_n)
      //( ((gen_proc.imem_bus_if.MCmd == Bus::RD) && gen_proc.imem_bus_if.SCmdAccept,
        //addr = gen_proc.imem_bus_if.MAddr)
        //##[1:$] ((gen_proc.imem_bus_if.SResp == Bus::DVA)
                 //&& gen_proc.imem_bus_if.MRespAccept
                 //&& (gen_proc.imem_bus_if.SData == proc_mem.mem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[addr]),
          //data = gen_proc.imem_bus_if.SData,
          //exp = proc_mem.mem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[addr],
            //$display("%08d : SData = %08h, memory[%08h] = %08h %s",
                //$time,
                //gen_proc.imem_bus_if.SData, addr, proc_mem.mem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[addr],
                //(gen_proc.imem_bus_if.SData == proc_mem.mem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[addr]) ? "good" : "bad"))
        //|-> 1 );
    //endproperty

    //sequence imem_req(addr, data);
      //((gen_proc.imem_bus_if.MCmd == Bus::RD) && gen_proc.imem_bus_if.SCmdAccept),
      //addr = gen_proc.imem_bus_if.MAddr,
      //data = proc_mem.mem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[gen_proc.imem_bus_if.MAddr] ;
    //endsequence

    //property cache_fetch_correctness_2;
      //int addr;
      //int exp_data;

      //@(posedge gen_proc.imem_bus_if.Clk) disable iff(!gen_proc.imem_bus_if.MReset_n)
      //( (imem_req(addr, exp_data) ##[1:$]) [* 1:$] 
        //|-> imem_resp
    //endproperty

    //check_cache_fetch_correctness: assert property(cache_fetch_correctness)
    //else
      //$error("cache retrieving incorrect instructions while fetching");

    //property cache_store_correctness;
      //int addr;

      //@(posedge clk) disable iff(reset || core_reset || !USE_PROCESSOR)
      //( (gen_proc.cache_store_w.en,addr = gen_proc.cache_store_w.addr)
        //|-> (gen_proc.cache_store_w.data_w == proc_mem.mem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[addr])
        //)
    //endproperty

  `endif /** SYNTHESIS */
  

  //---------------------------------------------------------------------------
  // Peripherals
  //---------------------------------------------------------------------------

  //Bus_if #(.byteen(1'b1)) bus_cregs_dummy(.Clk(clk));

  ////Bus_master_terminator terminate_bus_cregs_dummy(bus_cregs_dummy);
  //assign 
    //bus_cregs_dummy.MReset_n = ~reset,
    //bus_cregs_dummy.MCmd = Bus::IDLE;

  Bus_reg_target #(
    .NUM_REGS(1),
    .BASE_ADDR  (32'h1000_0000),
    .BASE_MASK  (32'hffff_ffff),
    .OFFSET_MASK(32'h0000_0001)
  ) cregs_target (
    .bus(bus_cregs),
    .regs_in(cregs),
    .regs(cregs)
  );

  //Freq_synth #(
    ////.BASE_ADDR(32'h2000_0000),
    ////.BASE_MASK(32'hffff_ffff),
    //.DCM_M(4),
    //.DCM_D(10),
    //.PLL_M(20),
    //.PLL_D_FAST(2),
    //.PLL_D_SLOW(8),
    //.CLK_FROM_IBUFG_PERIOD_NS(10.0)
  //) freq_synth (
    //.clk_from_ibufg,
    //.resetb_pin(resetb),
    //.clk_out_pin(gen_clk),
    //.reset_out(),
    //.bus(bus_freq_synth)
  //);

  // terminate missing Bus slaves
  //Bus_slave_terminator terminate_cregs(bus_cregs);
  Bus_slave_terminator terminate_freq_synth(bus_freq_synth);
  Bus_slave_terminator terminate_jtag(bus_jtag);


  assign
    sl_tdi = 1'b0,
    sl_tms = 1'b0,
    sl_tck = 1'b0;

  //---------------------------------------------------------------------------
  // LEDs & other outputs
  //---------------------------------------------------------------------------
 
  generate
    genvar i;
    for(i=0; i<4; i++) begin : gen_leds

      assign gpled[i] = pu_goe[i] ? pu_gout[i] : 1'bz;
      assign pu_gin[i] = gpled[i];

    end : gen_leds

    for(i=0; i<4; i++) begin : gen_sl_io

      assign sl_gpio[i] = pu_goe[i+4] ? pu_gout[i+4] : 1'bz;
      assign pu_gin[i+4] = sl_gpio[i];

    end : gen_sl_io

  endgenerate
   
  assign feten = 1'b1;

  assign status_led = ~reset & ~core_reset;
endmodule



/** JTAG input adapter. Connects to the internal BSCAN module and generates
* bus requests from the JTAG inputs. The controller uses one instruction and
* a 65 bit data register: 
*   <1-bit: read/not write><32-bit: address><32-bit: data>
* */
module Jtag_input
  ( input logic reset,
    Bus_if.master bus );

  Jtag_if jtag_if();
  Ram_if #(.ADDR_WIDTH(32), .DATA_WIDTH(32)) ram_if();

  Jtag #(.CHAIN(1)) jtag(.intf(jtag_if));
  
  Jtag_to_mem #(
    .NUM_SYNC_STAGES(1),
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32)
  ) jtag_to_mem (
    .clk(bus.Clk),
    .reset,
    .mem(ram_if),
    .jtag(jtag_if)
  );


  //---------------------------------------------------------------------------
  // State machine to generate bus access
  //---------------------------------------------------------------------------
  
  localparam readback_clear_value = 32'hdead_dead;

  logic on_state;
  logic readback_en, readback_clear;
  logic[31:0] readback_reg;

  /** state transitions
  * Keep on state until bus accepts the request */
  always_ff @(posedge bus.Clk or posedge reset)
    if( reset == 1'b1 ) begin
      on_state <= 1'b0;
    end else begin
      if( on_state == 1'b0 ) begin
        if( ram_if.en )
          on_state <= 1'b1;
      end else if( on_state == 1'b1 ) begin
        if( bus.SCmdAccept )
          on_state <= 1'b0;
      end else begin
        on_state <= 1'bx;
      end
    end

  /** output logic */
  always_ff @(posedge bus.Clk or posedge reset)
    if( reset ) begin
      bus.MAddr <= '0;
      bus.MData <= '0;
      bus.MCmd <= Bus::IDLE;
      bus.MDataValid <= 1'b0;
      //bus.MRespAccept <= 1'b0;
      bus.MByteEn <= '0;
    end else begin
      unique case(on_state)
        1'b0: begin
          if( ram_if.en && ram_if.we ) begin
            bus.MAddr <= ram_if.addr;
            bus.MData <= ram_if.data_w;
            bus.MCmd <= Bus::WR;
            bus.MDataValid <= 1'b1;
            bus.MByteEn <= ram_if.be;
            //bus.MRespAccept <= 1'b1;
          end else if( ram_if.en && !ram_if.we ) begin
            bus.MAddr <= ram_if.addr;
            bus.MData <= ram_if.data_w;
            bus.MCmd <= Bus::RD;
            bus.MDataValid <= 1'b0;
            bus.MByteEn <= '1;
            //bus.MRespAccept <= 1'b1;
          end
        end

        1'b1: begin
          if( bus.SCmdAccept ) begin
            bus.MAddr <= '0;
            bus.MData <= '0;
            bus.MCmd <= Bus::IDLE;
            bus.MDataValid <= 1'b0;
            bus.MByteEn <= '0;
          end
        end

        default: begin
          bus.MCmd <= Bus::Ocp_cmd'('x);
          bus.MDataValid <= 1'bx;
          //bus.MRespAccept <= 1'bx;
          bus.MByteEn <= 'x;
        end
      endcase
    end

  /** async control signals for result readback */
  assign readback_clear = on_state && !(bus.SResp == Bus::DVA);
  assign readback_en = (bus.SResp == Bus::DVA);


  /** readback register to store the response from the bus for later JTAG
  * capture */
  always_ff @(posedge bus.Clk or posedge reset)
    if( reset )
      readback_reg <= readback_clear_value;
    else begin
      if( readback_clear )
        readback_reg <= readback_clear_value;
      else if( readback_en )
        readback_reg <= bus.SData;
    end

  assign bus.MReset_n = ~reset;
  assign bus.MRespAccept = 1'b1;
  assign ram_if.data_r = readback_reg;

endmodule


/** A block of memory with read/write port using the Bus_if interface.
* Implemented as Virtex5 BlockRAMs */
module Memory_block
  #(parameter int ADDR_WIDTH = 13)
  ( Bus_if.slave bus );

  Ram_if #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(32)) mem_if();
  Ram_if #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(32)) mem_if_dummy();


  //Iobus_dummy #(
    //.RD_ACCEPT_LATENCY(0),
    //.WR_ACCEPT_LATENCY(0),
    //.RD_RETURN_LATENCY(1),
    //.WR_RETURN_LATENCY(1),
    //.RESPONSE_FUNCTION(1),  // memory
    //.BYTE_ENABLED(1'b1)
  //) mem_dummy (
    //.clk(bus.Clk),
    //.reset(~bus.MReset_n),
    //.iobus(bus)
  //);
    

  Bridge_bus2ram bus2ram(
    .bus_if(bus),
    .ram_if(mem_if)
  );

  //Bus_slave_terminator terminate_bus(bus);

  assign
    mem_if_dummy.en = 1'b0,
    mem_if_dummy.we = 1'b0;

  L1_memory #(
	.ADDR_WIDTH(ADDR_WIDTH)
  ) mem (
	.clk(bus.Clk),
	.reset(~bus.MReset_n),
	.intf(mem_if),
	.intf2(mem_if_dummy)
  );

  //L1_memory_dw #(
    //.ADDR_WIDTH(ADDR_WIDTH)
  //) mem (
    //.clk(bus.Clk),
    //.reset(~bus.MReset_n),
    //.intf(mem_if)
  //);

  //Sim_memory #(
    //.ADDR_WIDTH(13),
    //.DATA_WIDTH(32)
  //) mem (
    //.clk(bus.Clk),
    //.reset(~bus.MReset_n),
    //.intf(mem_if)
  //);

  `ifndef SYNTHESIS
    check_addr_range: assert property(
      @(posedge bus.Clk) disable iff(!bus.MReset_n)
      ( bus.MCmd != Bus::IDLE |-> (unsigned'(bus.MAddr) < unsigned'(2**ADDR_WIDTH)) )
    ) else
      $fatal("memory access to 0x%08h out of range (%0d-bits: < 0x%08h)",
        bus.MAddr, ADDR_WIDTH, 2**ADDR_WIDTH);      
  `endif /** SYNTHESIS */


endmodule

