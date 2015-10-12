// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Pu_types::*;

module Pu_test
	#(	IMEM_ADDR_WIDTH = 10,
		DMEM_ADDR_WIDTH = 10 ); 

const time clk_period = 10ns;
logic clk;
logic reset;

Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_if();
Ram_if #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_if();

L1_memory #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem 
	(	.clk(clk),
		.reset(reset),
		.intf(imem_if) );

L1_memory #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem
	(	.clk(clk),
		.reset(reset),
		.intf(dmem_if) );

Pu uut(
	.clk(clk),
	.reset(reset),
	.imem(imem_if),
	.dmem(dmem_if)
);


always #(clk_period/2) clk = ~clk;

initial begin
	$readmemh("test/testcode/interlocks_code.mem", imem.mem);
	$readmemh("test/testcode/interlocks.mem", dmem.mem);

	reset = '1;
	clk = '0;

	@(negedge clk);
	#(10*clk_period) reset = '0;
end

endmodule

