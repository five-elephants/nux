// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module L1_memory
	#(	parameter integer  ADDR_WIDTH = 10,
		                   DATA_WIDTH = 32,
		           bit     IS_DUALPORT = 1'b1 )

	(	input logic    clk,
		               reset,

		Ram_if.memory  intf,
		Ram_if.memory  intf2 );
	
	localparam MEM_SIZE = 2**ADDR_WIDTH;
	localparam integer BYTE_COUNT = DATA_WIDTH/8 + ((DATA_WIDTH%8 ==0) ? 0 : 1);

	generate 
		if( ADDR_WIDTH == 5 )
		begin : gen_addr_5bit
			logic[3:0] wea, web;

			assign wea = {4{intf.we}} & intf.be;
			assign web = {4{intf2.we}} & intf2.be;

			assign intf.delay = 1'b0;
			assign intf2.delay = 1'b0;

			ramb_32x32_dp ramb_inst (
				.clka(clk),
				.rsta(reset),
				.ena(intf.en),
				.wea(wea),
				.addra(intf.addr),
				.dina(intf.data_w),
				.douta(intf.data_r),

				.clkb(clk),
				.rstb(reset),
				.enb(intf2.en),
				.web(web),
				.addrb(intf2.addr),
				.dinb(intf2.data_w),
				.doutb(intf2.data_r)
			);

		end : gen_addr_5bit
		if( ADDR_WIDTH == 6 )
		begin : gen_addr_6bit
			logic[3:0] wea, web;

			assign wea = {4{intf.we}} & intf.be;
			assign web = {4{intf2.we}} & intf2.be;

			assign intf.delay = 1'b0;
			assign intf2.delay = 1'b0;

			ramb_64x32_dp ramb_inst (
				.clka(clk),
				.rsta(reset),
				.ena(intf.en),
				.wea(wea),
				.addra(intf.addr),
				.dina(intf.data_w),
				.douta(intf.data_r),

				.clkb(clk),
				.rstb(reset),
				.enb(intf2.en),
				.web(web),
				.addrb(intf2.addr),
				.dinb(intf2.data_w),
				.doutb(intf2.data_r)
			);

		end : gen_addr_6bit
		else if( ADDR_WIDTH == 7 )
		begin : gen_addr_7bit
			logic[3:0] wea, web;

			assign wea = {4{intf.we}} & intf.be;
			assign web = {4{intf2.we}} & intf2.be;

			assign intf.delay = 1'b0;
			assign intf2.delay = 1'b0;

			ramb_128x32_dp ramb_inst (
				.clka(clk),
				.rsta(reset),
				.ena(intf.en),
				.wea(wea),
				.addra(intf.addr),
				.dina(intf.data_w),
				.douta(intf.data_r),

				.clkb(clk),
				.rstb(reset),
				.enb(intf2.en),
				.web(web),
				.addrb(intf2.addr),
				.dinb(intf2.data_w),
				.doutb(intf2.data_r)
			);

		end : gen_addr_7bit
		else if( ADDR_WIDTH == 8 )
		begin : gen_addr_8bit
			logic[3:0] wea, web;

			assign wea = {4{intf.we}} & intf.be;
			assign web = {4{intf2.we}} & intf2.be;

			assign intf.delay = 1'b0;
			assign intf2.delay = 1'b0;

			ramb_256x32_dp ramb_inst (
				.clka(clk),
				.rsta(reset),
				.ena(intf.en),
				.wea(wea),
				.addra(intf.addr),
				.dina(intf.data_w),
				.douta(intf.data_r),

				.clkb(clk),
				.rstb(reset),
				.enb(intf2.en),
				.web(web),
				.addrb(intf2.addr),
				.dinb(intf2.data_w),
				.doutb(intf2.data_r)
			);

		end: gen_addr_8bit
		else if( ADDR_WIDTH == 9 )
		begin : gen_addr_9bit
			logic[3:0] wea, web;

			assign wea = {4{intf.we}} & intf.be;
			assign web = {4{intf2.we}} & intf2.be;

			assign intf.delay = 1'b0;
			assign intf2.delay = 1'b0;

			ramb_512x32_dp ramb_inst (
				.clka(clk),
				.rsta(reset),
				.ena(intf.en),
				.wea(wea),
				.addra(intf.addr),
				.dina(intf.data_w),
				.douta(intf.data_r),

				.clkb(clk),
				.rstb(reset),
				.enb(intf2.en),
				.web(web),
				.addrb(intf2.addr),
				.dinb(intf2.data_w),
				.doutb(intf2.data_r)
			);
			
		end : gen_addr_9bit
		else if( ADDR_WIDTH == 10 )
		begin : gen_addr_10bit
			// synthesis translate_off
			initial begin
				check_size: assert (2**ADDR_WIDTH * DATA_WIDTH <= 32*1024);
				check_width: assert (DATA_WIDTH <= 32);
			end
			// synthesis translate_on

			logic[15:0] addra, addrb;
			logic[3:0] wea, web;

			assign addra = {1'b1, intf.addr,  5'b11111};
			assign addrb = {1'b1, intf2.addr, 5'b11111};
			assign wea = {4{intf.we}} & intf.be;
			assign web = {4{intf2.we}} & intf2.be;

			assign intf.delay = 1'b0;
			assign intf2.delay = 1'b0;

			RAMB36 #(
				.SIM_MODE("SAFE"), // Simulation: "SAFE" vs. "FAST", see "Synthesis and Simulation Design Guide" for details
				.DOA_REG(0), // Optional output registers on A port (0 or 1)
				.DOB_REG(0), // Optional output registers on B port (0 or 1)
				.INIT_A(36'h000000000), // Initial values on A output port
				.INIT_B(36'h000000000), // Initial values on B output port
				.RAM_EXTENSION_A("NONE"), // "UPPER", "LOWER" or "NONE" when cascaded
				.RAM_EXTENSION_B("NONE"), // "UPPER", "LOWER" or "NONE" when cascaded
				.READ_WIDTH_A(36), // Valid values are 1, 2, 4, 9, 18, or 36
				.READ_WIDTH_B(36), // Valid values are 1, 2, 4, 9, 18, or 36
				.SIM_COLLISION_CHECK("ALL"), // Collision check enable "ALL", "WARNING_ONLY",
											 // "GENERATE_X_ONLY" or "NONE"
				.SRVAL_A(36'h000000000), // Set/Reset value for A port output
				.SRVAL_B(36'h000000000), // Set/Reset value for B port output
				.WRITE_MODE_A("READ_FIRST"), // "WRITE_FIRST", "READ_FIRST", or "NO_CHANGE"
				.WRITE_MODE_B("READ_FIRST"), // "WRITE_FIRST", "READ_FIRST", or "NO_CHANGE"
				.WRITE_WIDTH_A(36), // Valid values are 1, 2, 4, 9, 18, or 36
				.WRITE_WIDTH_B(36) // Valid values are 1, 2, 4, 9, 18, or 36
			) RAMB36_inst (
				.CASCADEOUTLATA(), // 1-bit cascade A latch output
				.CASCADEOUTLATB(), // 1-bit cascade B latch output
				.CASCADEOUTREGA(), // 1-bit cascade A register output
				.CASCADEOUTREGB(), // 1-bit cascade B register output
				.DOA(intf.data_r), // 32-bit A port data output
				.DOB(intf2.data_r), // 32-bit B port data output
				.DOPA(), // 4-bit A port parity data output
				.DOPB(), // 4-bit B port parity data output
				.ADDRA(addra), // 16-bit A port address input
				.ADDRB(addrb), // 16-bit B port address input
				.CASCADEINLATA(1'b0), // 1-bit cascade A latch input
				.CASCADEINLATB(1'b0), // 1-bit cascade B latch input
				.CASCADEINREGA(1'b0), // 1-bit cascade A register input
				.CASCADEINREGB(1'b0), // 1-bit cascade B register input
				.CLKA(clk),  // 1-bit A port clock input
				.CLKB(clk),  // 1-bit B port clock input
				.DIA(intf.data_w),    // 32-bit A port data input
				.DIB(intf2.data_w),    // 32-bit B port data input
				.DIPA(4'b0),  // 4-bit A port parity data input
				.DIPB(4'b0),  // 4-bit B port parity data input
				.ENA(intf.en),    // 1-bit A port enable input
				.ENB(intf2.en),    // 1-bit B port enable input
				.REGCEA(1'b1), // 1-bit A port register enable input
				.REGCEB(1'b1), // 1-bit B port register enable input
				.SSRA(reset),  // 1-bit A port set/reset input
				.SSRB(reset),  // 1-bit B port set/reset input
				.WEA(wea),    // 4-bit A port write enable input
				.WEB(web)     // 4-bit B port write enable input
			);

		end : gen_addr_10bit
		else if( ADDR_WIDTH == 13 ) 
		begin : gen_addr_13bit
			logic[3:0] wea, web;

			assign wea = {4{intf.we}} & intf.be;
			assign web = {4{intf2.we}} & intf2.be;

			assign intf.delay = 1'b0;
			assign intf2.delay = 1'b0;

			ramb_8192x32_dp ramb_inst (
				.clka(clk),
				.rsta(reset),
				.ena(intf.en),
				.wea(wea),
				.addra(intf.addr),
				.dina(intf.data_w),
				.douta(intf.data_r),

				.clkb(clk),
				.rstb(reset),
				.enb(intf2.en),
				.web(web),
				.addrb(intf2.addr),
				.dinb(intf2.data_w),
				.doutb(intf2.data_r)
			);

		end : gen_addr_13bit
	endgenerate


endmodule
