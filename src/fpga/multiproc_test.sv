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

module Multiproc_test();
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
	logic status_led;
	logic[3:0] gpled;

	logic sleep;
	logic[31:0] mon_pc;
	logic heartbeat;

	// JTAG pins
	Jtag_pin_if jtag();
	Jtag_v5_simpins jtag_pins(.pins(jtag));

	Multiproc_top uut(.*);

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

  task set_reset(input int num_elem, bit val);
    Jtag_request_t req; 
    Jtag_request_bits_t req_bits;
   
    req.we = 1'b1;
    req.addr = 32'h8000_0000 + num_elem;
    req.data = {31'b0, val};

    req_bits = {<<{req}};
    jtag_trans.load_data(req_bits);
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

    // enable all elements
    for(int i=0; i<2/*6*/; i++)
      set_reset(i, 1'b0);

		#(40000 * clk_period); // wait 200 us

    //// disable all elements
    //for(int i=0; i<6; i++)
      //set_reset(i, 1'b1);

    //rw_test(32'h00_00_0000, 32'h00_00_0010);
    //rw_test(32'h00_01_0000, 32'h00_01_0010);
    //rw_test(32'h01_00_0000, 32'h01_00_0010);
    //rw_test(32'h01_01_0000, 32'h01_01_0010);
    //rw_test(32'h02_00_0000, 32'h02_00_0010);
    //rw_test(32'h02_01_0000, 32'h02_01_0010);

    //rw_test(32'h03_00_0000, 32'h03_00_0010);
    //rw_test(32'h03_01_0000, 32'h03_01_0010);
    //rw_test(32'h04_00_0000, 32'h04_00_0010);
    //rw_test(32'h04_01_0000, 32'h04_01_0010);
    //rw_test(32'h05_00_0000, 32'h05_00_0010);
    //rw_test(32'h05_01_0000, 32'h05_01_0010);

    //rw_test(16'h0000, 16'h0010);
    //rw_test(16'h4000, 16'h4010);
    //rw_test(16'h8000, 16'h8010);
    //rw_test(16'hc000, 16'hc010);



    //$stop;
	end


endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
