// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Processor_if();
  import jtag_pkg::Imem_addr;
  import jtag_pkg::Imem_data;
  import jtag_pkg::Dmem_addr;
  import jtag_pkg::Dmem_data;

  //---------------------------------------------------------------------------
  // signals
  //---------------------------------------------------------------------------
  
  logic         en;    // global enable signal
  logic         hold;  // hold signal
  logic         sleep_status;

  logic         clk_force_on;
  logic         clk_force_off;

  // instruction memory programming interface
  logic         imem_we;
  logic         imem_re;
  Imem_addr     imem_addr;
  Imem_data     imem_data_w;
  Imem_data     imem_data_r;

  // data memory programming interface
  logic         dmem_we;
  logic         dmem_re;
  Dmem_addr     dmem_addr;
  Dmem_data     dmem_data_w;
  Dmem_data     dmem_data_r;

  // Breakpoint registers
  Imem_addr     inst_break;
  logic         inst_break_en;
  logic         inst_break_pc_en;

  Dmem_addr     data_break;
  logic         data_break_wr_en;
  logic         data_break_rd_en;

  logic         break_continue;
  logic         break_status;

  // doorbell interrupt
  logic         doorbell;

  // monitoring signals
  logic[31:0]   mon_inst;
  logic[31:0]   mon_pc;

  //---------------------------------------------------------------------------
  // modport definitions
  //---------------------------------------------------------------------------

  modport jtag (
    output en, hold, clk_force_on, clk_force_off,

    output imem_we, imem_re, imem_addr, imem_data_w,
    input imem_data_r,
    output dmem_we, dmem_re, dmem_addr, dmem_data_w,
    input dmem_data_r,
    output inst_break, inst_break_en, inst_break_pc_en, 
      data_break, data_break_wr_en, 
      data_break_rd_en, break_continue,
    input break_status, sleep_status,
    output doorbell,
    input mon_inst, mon_pc
  );

  modport proc (
    input en, hold, clk_force_on, clk_force_off,

    input imem_we, imem_re, imem_addr, imem_data_w,
    output imem_data_r,
    input dmem_we, dmem_re, dmem_addr, dmem_data_w,
    output dmem_data_r,
    input inst_break, inst_break_en, inst_break_pc_en,
      data_break, data_break_wr_en, 
      data_break_rd_en, break_continue,
    output break_status, sleep_status,
    input doorbell,
    output mon_inst, mon_pc
  );
endinterface
