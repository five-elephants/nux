// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module Break
  ( input logic clk, reset,

    Ram_if.monitor     imem_mon,
    Ram_if.monitor     dmem_mon,
    input logic[31:0]  pc_mon,
    input logic        mon_hold_dc,
    Processor_if.proc  ctrl,

    output logic       stop_clk );

logic is_continued;
logic is_stopped;
logic stop_clk_i;

always_comb begin
  //default assignment
  stop_clk_i = 1'b0;

  if( ctrl.break_continue && !is_continued )
    stop_clk_i = 1'b0;
  else if( is_stopped )
    stop_clk_i = 1'b1;
  else begin
    if( ctrl.inst_break_pc_en
        && (pc_mon == ctrl.inst_break)
        && (mon_hold_dc == 1'b0) )
      stop_clk_i = 1'b1;

    if( ctrl.inst_break_en 
        && (imem_mon.addr == ctrl.inst_break)
        && (imem_mon.en == 1'b1) )
      stop_clk_i = 1'b1;

    if( ctrl.data_break_rd_en
        && (dmem_mon.addr == ctrl.data_break)
        && (dmem_mon.en == 1'b1) )
      stop_clk_i = 1'b1;

    if( ctrl.data_break_wr_en
        && (dmem_mon.addr == ctrl.data_break)
        && (dmem_mon.en == 1'b1)
        && (dmem_mon.we == 1'b1) )
      stop_clk_i = 1'b1;
  end
end

//assign stop_clk = stop_clk_i;
always_ff @(posedge clk or posedge reset)
  if( reset )
    stop_clk <= 1'b0;
  else
    stop_clk <= stop_clk_i;

always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    is_continued <= 1'b0;
    is_stopped <= 1'b0;
  end else begin
    is_continued <= ctrl.break_continue;
    is_stopped <= stop_clk_i;
  end

endmodule
