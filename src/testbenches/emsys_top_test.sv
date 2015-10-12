// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


timeunit 1ns;
timeprecision 10ps;

import Pu_types::*;

module Emsys_top_test();
  const time clk_period = 10ns;
  const time jtag_clk_period = 100ns;

  localparam int JTAG_ADDR_WIDTH = 32;
  localparam int JTAG_DATA_WIDTH = 32;

  typedef struct {
    logic we;
    logic[JTAG_ADDR_WIDTH-1:0] addr;
    logic[JTAG_DATA_WIDTH-1:0] data;
  } Jtag_request_t;

  typedef logic Jtag_request_bits_t[0:$bits(Jtag_request_t)-1];

  logic clk, resetb;

  // processor toplevel signals
  logic sl_tdo;
  logic sl_tdi;
  logic sl_tms;
  logic sl_tck;
  wire sl_gpio[3:0];

  logic gen_clk;
  logic feten;
  logic status_led;
  logic[3:0] gpled;

  logic sleep;
  logic heartbeat;

  // JTAG pins
  Jtag_pin_if jtag();
  Jtag_v5_simpins jtag_pins(.pins(jtag));

  Emsys_top uut(
    .clk_in(clk),
    .*
  );

	//---------------------------------------------------------------------------
	/** clock generation */
	always begin
		#(clk_period/2) clk = 1;
		#(clk_period/2) clk = 0;
	end

	always begin
		#(jtag_clk_period/2) jtag.tck = 1'b0;
		#(jtag_clk_period/2) jtag.tck = 1'b1;
	end
	//---------------------------------------------------------------------------

  `include "jtag_trans.sv"

  Jtag_trans jtag_trans;
	const logic[9:0] JI_USER1 = 10'b1111000010;
	const logic[9:0] JI_USER2 = 10'b1111000011;
	const logic[9:0] JI_USER3 = 10'h3e2;

  //---------------------------------------------------------------------------
  // Testbench stimulation generation code
  //---------------------------------------------------------------------------
 
  task rw_test(input int addr_start, addr_stop);
    Jtag_request_t req; 
    Jtag_request_bits_t req_bits;
    Jtag_request_t resp;
    Jtag_request_bits_t resp_bits;
    int data[];
    int data_r;
    
    data = new [addr_stop - addr_start +1];

    for(int i=addr_start; i<=addr_stop; i++) begin
      data[i-addr_start] = $urandom;

      req.we = 1'b1;
      req.addr = i;
      req.data = data[i-addr_start];

      req_bits = {<<{req}};

      jtag_trans.load_data(req_bits);
    end

    req.we = 1'b0;
    req.addr = addr_start;
    req.data = '0;
    req_bits = {<<{req}};

    jtag_trans.load_data(req_bits);

    for(int i=addr_start; i<=addr_stop; i++) begin
      if( i+1 <= addr_stop )
        req.addr = i+1;

      req_bits = {<<{req}};
      jtag_trans.load_data_read(req_bits, resp_bits); 

      resp = Jtag_request_t'({<<{resp_bits}});
      data_r = resp.data;

      check_rw_test: assert(data_r === data[i-addr_start]) else
        $error("Read/write test failed at %08h (expected %08h, got %08h)",
          i, data[i-addr_start], data_r);
    end
  endtask


  task write(input int addr, data);
    Jtag_request_t req; 
    Jtag_request_bits_t req_bits;

    req.we = 1'b1;
    req.addr = addr;
    req.data = data;

    req_bits = {<<{req}};

    jtag_trans.load_data(req_bits);
  endtask

  task read(input int addr, output int data);
    Jtag_request_t req; 
    Jtag_request_bits_t req_bits;
    Jtag_request_t resp;
    Jtag_request_bits_t resp_bits;

    req.we = 1'b0;
    req.addr = addr;
    req.data = '0;
    req_bits = {<<{req}};
    
    jtag_trans.load_data(req_bits);
    jtag_trans.load_data_read(req_bits, resp_bits); 

    resp = Jtag_request_t'({<<{resp_bits}});
    data = resp.data;
  endtask

  task load_program(input string image_file);
    Word img[];

    img = new [2**13];

    Program_pkg::read_raw_image(image_file, img);

    foreach(img[i])
      uut.proc_mem.mem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[i] = img[i];
  endtask

  //---------------------------------------------------------------------------
	initial begin
		logic tmp_inst[0:9];  // (verilog sucks)

    jtag_trans = new(jtag);

		clk = 1'b1;
		jtag.tck = 1'b0;
    resetb = 1'b0;

    @(negedge clk);

    //#(10*clk_period) resetb = 1'b1;
    //#(2200ns) resetb = 1'b1;  // wait until JTAG instruction is loaded and
                  // BSCAN_VIRTEX5 outputs are all in a defined
                  // state

    // move JTAG to reset state
    jtag_trans.reset();
    jtag_trans.reset_to_idle();
    for(int i=0; i<10; i++) tmp_inst[i] = JI_USER1[i];
    jtag_trans.load_instruction(tmp_inst);

    resetb = 1'b1;

    #(500ns);

    //write(32'h3001_0000, 32'h0000_0001);    // enable gen_clk
    //write(32'h3001_0000, 32'h0000_0003);    // select fast clk
    //write(32'h3001_0000, 32'h0000_0000);    // disable gen_clk

    write(32'h1000_0000, 32'h0000_0000);    // reset core
    $display("ramtest with disabled core");
    rw_test(32'h0000_0000, 32'h0000_0010);
    rw_test(32'h0000_1000, 32'h0000_1010);  // ramtest
    //write(32'h1000_0000, 32'h0000_0001);    // release core reset
    //$display("ramtest with enabled core");
    //rw_test(32'h0000_1000, 32'h0000_1010);  // ramtest
    //write(32'h1000_0000, 32'h0000_0000);    // reset core

    $display("loading a program");
    //load_program("/afsuser/sfriedma/s2pp_testing/programs/coremark_single_img.raw");
    load_program("/afsuser/sfriedma/s2pp_testing/programs/coremark_single_img_single_iteration.raw");
    write(32'h1000_0000, 32'h0000_0001);    // release core reset

    @(sleep);
    $display("program finished");

    $stop;
  end
endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
