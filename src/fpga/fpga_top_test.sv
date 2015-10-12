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

localparam int MEM_SIZE = 2**13;

module Fpga_top_test () ;
	const time clk_period = 10ns;
	const time jtag_clk_period = 100ns;

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

	Fpga_top uut(.*);

	//`include "../../__ram_boot_img.v"

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

	initial begin
		clk = 1'b1;
		jtag.tck = 1'b0;
		//resetb = 1'b0;
		//#(10*clk_period) resetb = 1'b1;
		//#(2200ns) resetb = 1'b1;  // wait until JTAG instruction is loaded and
								  // BSCAN_VIRTEX5 outputs are all in a defined
								  // state
	end

	//jtag_test jtag_test_inst();
	bootcode_test bootcode_test_inst(.jtag(jtag), .sleep, .resetb);
	//jtag_program jtag_program_inst(.jtag(jtag), .sleep);

endmodule



//---------------------------------------------------------------------------
/** Test program to test the JTAG functionality */
//program jtag_test(Jtag_pin_if jtag);
	//`include "jtag_trans.sv"

	//typedef logic Jtag_data[0:45];
	//typedef logic[12:0] Addr;

	//Jtag_trans jtag_trans;
	//const logic[9:0] JI_USER1 = 10'h3c2;
	//const logic[9:0] JI_USER2 = 10'h3c3;
	//const logic[9:0] JI_USER3 = 10'h3e2;
	////---------------------------------------------------------------------------
	//// XXX Clocking blocks driving interface signals don't seem to work with
	//// Modelsim 6.5b
	//default clocking cb_jtag @(posedge jtag.tck);
		//default input #1step output negedge;
	//endclocking
	////---------------------------------------------------------------------------

	////---------------------------------------------------------------------------
	//function automatic void mem_access(input Addr addr, Word data, logic we, ref Jtag_data jtag_data);
		//for(int i=0; i<32; i++)
			//jtag_data[i] = data[i];

		//for(int i=0; i<$bits(Addr); i++)
			//jtag_data[32+i] = addr[i];

		//jtag_data[$right(jtag_data)] = we;
	//endfunction
	////---------------------------------------------------------------------------

	////---------------------------------------------------------------------------
	//initial begin
		//logic tmp_inst[0:9];  // (verilog sucks)
		//Jtag_data data;
		//Jtag_data rdata;
		//Jtag_data check_data;
		//logic ctrl_data[0:0];
		//Word test_img[0:MEM_SIZE-1];

		//jtag_trans = new(jtag);

		//jtag.tms <= 1'b1;
		//jtag.tdi <= 1'b0;

		//// perform tests
		//##(10) jtag_trans.reset();
		//jtag_trans.reset_to_idle();
		//for(int i=0; i<10; i++) tmp_inst[i] = JI_USER1[i];
		//jtag_trans.load_instruction(tmp_inst);

		//mem_access(0, 32'hdeadface, 1'b1, data);
		//jtag_trans.load_data(data);

		//mem_access(13'b1010001000, 32'haffeaffe, 1'b1, data);
		//jtag_trans.load_data(data);

		//// generate test image
		//for(int i=0; i<MEM_SIZE; i++) begin
			//test_img[i] = $random;
		//end

		//// write test image to memory
		//for(int addr=0; addr<MEM_SIZE; addr++) begin
			//mem_access(addr, test_img[addr], 1'b1, data);
			//jtag_trans.load_data(data);
		//end

		//// read memory and check versus test image
		//for(int addr=0; addr<MEM_SIZE; addr++) begin
			//mem_access(addr, test_img[addr]+1, 1'b1, data);
			//jtag_trans.load_data_read(data, rdata);

			//if( addr > 1 ) begin
				//mem_access(addr-1, test_img[addr-1], 1'b1, check_data);
				//check_write_dmem: assert(rdata === check_data)
					//else $error("JTAG ram-write failed. (Expected '%p', got '%p')",
							//check_data, rdata);
			//end
		//end

		//##(10);
		
		////// select instruction memory
		////for(int i=0; i<10; i++) tmp_inst[i] = JI_USER2[i];
		////jtag_trans.load_instruction(tmp_inst);

		////// perform ramtest
		////for(int addr='0; addr<1024; addr++) begin
			////mem_access(addr, $random, data);
			////jtag_trans.load_data_read(data, rdata);
			////check_write_imem: assert(addr == 0 || rdata === check_data)
				////else $error("JTAG ram-write failed. (Expected '%p', got '%p')",
						////check_data, rdata);
		////end

		//// check reset by JTAG
		//for(int i=0; i<10; i++) tmp_inst[i] = JI_USER3[i];
		//jtag_trans.load_instruction(tmp_inst);
		//ctrl_data[0] = 1'b1;
		//jtag_trans.load_data(ctrl_data);

		//##(10);
		//ctrl_data[0] = 1'b0;
		//jtag_trans.load_data(ctrl_data);

		//$stop;

	//end
	////---------------------------------------------------------------------------
//endprogram
////---------------------------------------------------------------------------

//---------------------------------------------------------------------------
program bootcode_test(Jtag_pin_if jtag, input logic sleep, output logic resetb);
	`include "jtag_trans.sv"

	Jtag_trans jtag_trans;
	const logic[9:0] JI_USER3 = 10'h3e2;
	
	//---------------------------------------------------------------------------
	// XXX Clocking blocks driving interface signals don't seem to work with
	// Modelsim 6.5b
	default clocking cb_jtag @(posedge jtag.tck);
		default input #1step output negedge;
	endclocking
	//---------------------------------------------------------------------------
	
	initial begin
		logic ctrl_data[0:0];
		logic tmp_inst[0:9];  // (verilog sucks)
		Word dump_img[];
		
		jtag_trans = new(jtag);

		resetb = 1'b0;

		// move JTAG to reset state
		jtag_trans.reset();
		jtag_trans.reset_to_idle();
		for(int i=0; i<10; i++) tmp_inst[i] = JI_USER3[i];
		jtag_trans.load_instruction(tmp_inst);
		
		##2000; // wait 200 us

		// set reset by JTAG
		ctrl_data[0] = 1'b1;
		jtag_trans.load_data(ctrl_data);

		##(10);
		ctrl_data[0] = 1'b0;
		jtag_trans.load_data(ctrl_data);

		##2000; // wait 200 us

		// test external reset
		resetb = 1'b0;

		// move JTAG to reset state
		jtag_trans.reset();
		jtag_trans.reset_to_idle();
		for(int i=0; i<10; i++) tmp_inst[i] = JI_USER3[i];
		jtag_trans.load_instruction(tmp_inst);

		##(10) resetb = 1'b1;  // release reset

		//##2000;
		@(sleep == 1'b1);

		dump_img = new [MEM_SIZE];
		
		for(int i=0; i<MEM_SIZE; i++)
			dump_img[i] = uut.dmem.gen_addr_13bit.ramb_inst.inst.blk_mem_gen_v4_3_inst.memory[i];

		Program_pkg::write_raw_image("dump_fpga_top_test_data.bin", dump_img);

		$stop;
	end
endprogram
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
/** Test program to test the JTAG functionality */
program jtag_program(Jtag_pin_if jtag, input logic sleep);
	`include "jtag_trans.sv"
	
	const string code_img_file = "test/testcode/coremark_v1.0/coremark_code.mem";
	const string data_img_file = "test/testcode/coremark_v1.0/coremark_data.mem";
	//const string code_img_file = "test/testcode/c/eblinker_code.mem";
	//const string data_img_file = "test/testcode/c/eblinker_data.mem";
	const time program_exe_time = 2ms;


	typedef logic Jtag_data[0:45];
	typedef logic[12:0] Addr;

	Jtag_trans jtag_trans;
	const logic[9:0] JI_USER1 = 10'h3c2;
	const logic[9:0] JI_USER2 = 10'h3c3;
	const logic[9:0] JI_USER3 = 10'h3e2;
	//---------------------------------------------------------------------------
	// XXX Clocking blocks driving interface signals don't seem to work with
	// Modelsim 6.5b
	default clocking cb_jtag @(posedge jtag.tck);
		default input #1step output negedge;
	endclocking
	//---------------------------------------------------------------------------

	//---------------------------------------------------------------------------
	function automatic void mem_access(input Addr addr, Word data, logic we, ref Jtag_data jtag_data);
		for(int i=0; i<32; i++)
			jtag_data[i] = data[i];

		for(int i=0; i<$bits(Addr); i++)
			jtag_data[32+i] = addr[i];

		jtag_data[$right(Jtag_data)] = we;
	endfunction
	//---------------------------------------------------------------------------

	//---------------------------------------------------------------------------
	initial begin : initial_block
		logic tmp_inst[0:9];  // (verilog sucks)
		Jtag_data data;
		Jtag_data rdata;
		Jtag_data check_data;
		logic ctrl_data[0:0];
		Word code_img[0:MEM_SIZE-1];
		Word data_img_byte[0:(4*MEM_SIZE)-1];
		Word result_img[0:599];
		int binf;
		Word w;

		jtag_trans = new(jtag);

		jtag.tms <= 1'b1;
		jtag.tdi <= 1'b0;

		// perform tests
		##(10) jtag_trans.reset();
		jtag_trans.reset_to_idle();
		for(int i=0; i<10; i++) tmp_inst[i] = JI_USER3[i];  // select control register
		jtag_trans.load_instruction(tmp_inst);

		// set reset by JTAG
		ctrl_data[0] = 1'b1;
		jtag_trans.load_data(ctrl_data);

		##(10);

		// load program image
		$readmemh(code_img_file, code_img);
		$readmemh(data_img_file, data_img_byte);

		// transfer to processor
		for(int i=0; i<10; i++) tmp_inst[i] = JI_USER2[i];  // select instruction memory
		jtag_trans.load_instruction(tmp_inst);

		for(int i=$left(code_img); i<=$right(code_img); i++) begin : load_code
			if( code_img[i] === 'x )
				continue;

			mem_access(i, code_img[i], 1'b1, data);
			jtag_trans.load_data(data);
		end

		for(int i=0; i<10; i++) tmp_inst[i] = JI_USER1[i];  // select data memory
		jtag_trans.load_instruction(tmp_inst);

		w = '0;
		for(int i=$left(data_img_byte); i<=$right(data_img_byte); i++) begin : load_data
			int byte_i;
			byte_i = 3 - (i % 4);

			w[8*(byte_i+1)-1 -: 8] = data_img_byte[i];

			if( (byte_i == 0) && !(w === 32'hxx_xx_xx_xx) ) begin
				//$display("sending: w=%08h", w);
				mem_access(i/4, w, 1'b1, data);
				jtag_trans.load_data(data);
				w = '0;
			end
		end

		// release reset
		for(int i=0; i<10; i++) tmp_inst[i] = JI_USER3[i];  // select control register
		jtag_trans.load_instruction(tmp_inst);
		ctrl_data[0] = 1'b0;
		jtag_trans.load_data(ctrl_data);

		// execute program
		//#(program_exe_time);
		@(sleep == 1'b1);

		// get results
		for(int i=0; i<10; i++) tmp_inst[i] = JI_USER1[i];  // select data memory
		jtag_trans.load_instruction(tmp_inst);

		binf = $fopen("result_img.bin", "w");
		for(int i=$left(result_img); i<=$right(result_img)+1; i++) begin : load_result
			mem_access(i, 32'h0, 1'b0, data);
			jtag_trans.load_data_read(data, rdata);
			//$display("rdata = %p", rdata);
			if( i > 0 ) begin
				for(int j=0;j<32;j++)
					result_img[i-1][j] = rdata[j];

				$fwrite(binf, "%u", {result_img[i-1][7:0],result_img[i-1][15:8],result_img[i-1][23:16],result_img[i-1][31:24]});
				//$fwrite(binf, "%u", result_img[i-1]);
			end
		end

		$fclose(binf);

		// check reset by JTAG
		for(int i=0; i<10; i++) tmp_inst[i] = JI_USER3[i];
		jtag_trans.load_instruction(tmp_inst);
		ctrl_data[0] = 1'b1;
		jtag_trans.load_data(ctrl_data);

		##(10);
		ctrl_data[0] = 1'b0;
		jtag_trans.load_data(ctrl_data);

		$stop;

	end
	//---------------------------------------------------------------------------
endprogram
//---------------------------------------------------------------------------

