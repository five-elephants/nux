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
import processor_pkg::*;

module Processor
  ( input logic clk, reset,
    input logic jtag_clk,
    Processor_if.proc        intf,
    Top_pin_digital_if.proc  dio );

  // synopsys translate_off
  always @(intf.en) begin
    if( intf.en == 1'b1 )
      $display("processor enabled");
    else
      $display("processor disabled");
  end
  // synopsys translate_on

  //---------------------------------------------------------------------------
  // Local signals
  //---------------------------------------------------------------------------
  
  logic proc_clk;
  //logic proc_clk_en_b;
  logic proc_clk_en;
  logic proc_reset;
  logic cg_sleep;
  logic cg_break;
  logic wakeup;

  Word gout;
  Word gin;
  Word goe;

  /** Clock gating for processor clock */
  /*always_ff @(posedge clk or posedge reset)
    if( reset )
      proc_clk_en_b <= 1'b0;
    else
      proc_clk_en_b <= (~wakeup & cg_sleep) | cg_break;*/
  //assign proc_clk = clk | proc_clk_en_b;

  always_latch
    if( !clk )
      proc_clk_en = (~((~wakeup & cg_sleep) | cg_break) & ~intf.clk_force_off) 
          | intf.clk_force_on;

  assign proc_clk = clk & proc_clk_en;
  //assign proc_clk = clk;
  assign cg_sleep = pu_ctrl.sleep;


  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      intf.sleep_status <= 1'b0;
      intf.break_status <= 1'b0;
    end else begin
      intf.sleep_status <= cg_sleep;
      intf.break_status <= cg_break;
    end

  /** Connect general purpose IO port */
  assign 
    gin[$left(gin):$left(dio.proc_in)+1] = '0,
    gin[$left(dio.proc_in):$right(dio.proc_in)] = dio.proc_in;

  assign dio.proc_out = gout[$left(dio.proc_out):$right(dio.proc_out)];
  assign dio.proc_oe = goe[$left(dio.proc_oe):$right(dio.proc_oe)];
    //dio.proc_ie = ~goe[$left(dio.proc_ie):$right(dio.proc_ie)];
  //assign dio.proc_ie = ~goe[$left(dio.proc_oe):$right(dio.proc_oe)];
  assign dio.proc_ie = '1;

  assign 
    intf.mon_inst = pu_ctrl.mon_inst,
    intf.mon_pc = pu_ctrl.mon_pc;

  assign proc_reset = ~intf.en;

  //---------------------------------------------------------------------------
  // submodules
  //---------------------------------------------------------------------------
 
  Pu_ctrl_if pu_ctrl();
  Timer_if   timer_if();
  Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_if();
  Ram_if #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_if();
  Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) jtag_imem_if();
  Ram_if #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) jtag_dmem_if();

  /*L1_memory #(
    .ADDR_WIDTH(IMEM_ADDR_WIDTH),
    .IS_DUALPORT(1'b1)
  ) imem ( 
    .clk(clk),
    .reset(reset),
    .intf(imem_if.memory),
    .intf2(jtag_imem_if.memory)
  );

  L1_memory #(
    .ADDR_WIDTH(DMEM_ADDR_WIDTH),
    .IS_DUALPORT(1'b1)
  ) dmem (
    .clk(clk),
    .reset(reset),
    .intf(dmem_if.memory),
    .intf2(jtag_dmem_if.memory) 
  );*/

  Sram_wrapper imem (
    .clk_a(proc_clk),
    .reset_a(reset),
    .clk_b(jtag_clk),
    .reset_b(1'b0),
    .port_a(imem_if.memory),
    .port_b(jtag_imem_if.memory)
  );

  Sram_wrapper dmem (
    .clk_a(proc_clk),
    .reset_a(reset),
    .clk_b(jtag_clk),
    .reset_b(1'b0),
    .port_a(dmem_if.memory),
    .port_b(jtag_dmem_if.memory)
  );

  Pu #(
    .OPT_GPR_ONE_WRITE_PORT(1'b0),
    .OPT_MULTIPLIER(1'b1),
    .OPT_DIVIDER(1'b1),
    .OPT_FORWARDING(1'b1)
  ) pcore (
    .clk(proc_clk),
    .reset(proc_reset),
    .hold(intf.hold),

    .imem(imem_if.client),
    .dmem(dmem_if.client),

    .gout(gout),
    .gin(gin),
    .goe(goe),
    //.gout({28'b0, dio.proc_out[3:0]}),
    //.gin({28'b0, dio.proc_in[3:0]}),
    //.goe({28'b0, dio.proc_oe[3:0]}),

    .ctrl(pu_ctrl.pu),
    .timer(timer_if.pu)
  );


  Jtag_to_mem jtag_to_mem (
    .imem(jtag_imem_if.client),
    .dmem(jtag_dmem_if.client),
    .jtag(intf)
  );

  Break brk (
    .clk(clk),
    .reset(proc_reset),
    .imem_mon(imem_if.monitor),
    .dmem_mon(dmem_if.monitor),
    .pc_mon(pu_ctrl.mon_pc),
    .mon_hold_dc(pu_ctrl.mon_hold_dc),
    .ctrl(intf),
    .stop_clk(cg_break)
  );

  Interrupt_ctrl interrupt_ctrl (
    .clk(clk),
    .reset(reset),
    .pu_ctrl(pu_ctrl.ctrl),
    //.ctrl(intf),
    .doorbell(intf.doorbell),
    .timer(timer_if.int_ctrl),
    .en_clk(wakeup),
    .gin(gin)
  );

  Timer_unit timer (
    .clk(clk),
    .reset(proc_reset),
    .intf(timer_if.timer)
  );

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
