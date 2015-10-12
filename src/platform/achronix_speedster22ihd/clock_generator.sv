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

	assign clk_out = clk_from_pin;
	assign reset_out = ~resetb_pin;

endmodule
