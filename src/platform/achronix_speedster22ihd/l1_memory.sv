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

localparam BRAM_DATA_WIDTH = 32;

logic[3:0] wea, web;

assign wea = {4{intf.we}} & intf.be;
assign web = {4{intf2.we}} & intf2.be;

BRAM80K #(
  .porta_read_width(BRAM_DATA_WIDTH),
  .porta_write_width(BRAM_DATA_WIDTH),
  .porta_write_mode("write_first"),
  .porta_clock_polarity("rise"),
  .porta_en_out_reg(1'b0),
  .porta_regce_priority("rstreg"),
  .porta_peval(1'b1),
  .porta_reg_rstval(1'b1),
  .porta_latch_rstval(1'b1),
  .porta_initval({BRAM_DATA_WIDTH{1'h0}}),
  .porta_srval({BRAM_DATA_WIDTH{1'h0}}),
  .portb_read_width(32),
  .portb_write_width(32),
  .portb_write_mode("write_first"),
  .portb_clock_polarity("rise"),
  .portb_en_out_reg(1'b0),
  .portb_regce_priority("rstreg"),
  .portb_peval(1'b1),
  .portb_reg_rstval(1'b1),
  .portb_latch_rstval(1'b1),
  .portb_initval({BRAM_DATA_WIDTH{1'h0}}),
  .portb_srval({BRAM_DATA_WIDTH{1'h0}})
) bram (
  .addra(intf.addr),
  .dina(intf.data_w),
  .dinpa('0),
  .dinpxa('0),
  .wea(wea),
  .pea(intf.en),
  .rstlatcha(reset),
  .rstrega(reset),
  .outregcea(intf.en),
  .clka(clk),
  .douta(intf.data_r),
  .doutpa(),
  .doutpxa(),
  .addrb(intf2.addr),
  .dinb(intf2.data_w),
  .dinpb('0),
  .dinpxb('0),
  .web(web),
  .peb(intf2.en),
  .rstlatchb(reset),
  .rstregb(reset),
  .outregceb(intf2.en),
  .clkb(clk),
  .doutb(intf2.data_r),
  .doutpb(),
  .doutpxb()
);

endmodule
