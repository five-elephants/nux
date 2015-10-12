// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module clock_generator
  #(parameter int MULTIPLICATOR = 1,
    parameter int DIVIDER = 2,
    parameter real CLK_PIN_PERIOD_NS = 10.0 )
  ( input logic clk_from_pin, resetb_pin,
    output logic clk_out, reset_out );


wire clk_from_ibufg;
wire clkfb;
wire clk_to_bufg;
wire gen_clk;
logic locked;
logic reset;
logic reset_sync;
logic reset_cond;

IBUFG clk_pin_ibufg (.I(clk_from_pin), .O(clk_from_ibufg));

/** Asynchronous reset synchronizer based on Cummings Paper */
always_ff @(posedge clk_from_ibufg or negedge resetb_pin)
	if( !resetb_pin )
		{reset, reset_sync} <= 2'b11;
	else
		{reset, reset_sync} <= {reset_sync, 1'b0};


PLL_BASE #(
  .CLKFBOUT_MULT(MULTIPLICATOR),
  .CLKOUT0_DIVIDE(DIVIDER),
  .CLKIN_PERIOD(CLK_PIN_PERIOD_NS)
) pll (
  .CLKIN(clk_from_ibufg),
  .RST(reset),
  .CLKFBOUT(clkfb),
  .CLKFBIN(clkfb),
  .CLKOUT0(clk_to_bufg),
  .CLKOUT1(),
  .CLKOUT2(),
  .CLKOUT3(),
  .CLKOUT4(),
  .CLKOUT5(),
  .LOCKED(locked)
);

BUFG gen_clk_bufg(.I(clk_to_bufg), .O(gen_clk));
assign clk_out = gen_clk;

assign reset_cond = ~locked | reset;

always_ff @(posedge gen_clk or posedge reset_cond)
  if( reset_cond )
    reset_out <= 1'b1;
  else
    reset_out <= 1'b0;


endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
