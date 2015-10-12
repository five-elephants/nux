// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module L1_memory_s6
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
		if( ADDR_WIDTH == 7 )
		begin : gen_addr_7bit

			logic[3:0] wea, web;

			assign wea = {4{intf.we}} & intf.be;
			assign web = {4{intf2.we}} & intf2.be;

			assign intf.delay = 1'b0;
			assign intf2.delay = 1'b0;

			sp6_ramb_128x32_dp ramb_inst (
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
		else if( ADDR_WIDTH == 13 ) 
		begin : gen_addr_13bit
			logic[3:0] wea, web;

			assign wea = {4{intf.we}} & intf.be;
			assign web = {4{intf2.we}} & intf2.be;

			assign intf.delay = 1'b0;
			assign intf2.delay = 1'b0;

			sp6_ramb_8192x32_dp ramb_inst (
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
