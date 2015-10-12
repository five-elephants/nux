// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Jtag_to_mem
	#(	parameter int NUM_SYNC_STAGES = 2,
		parameter int ADDR_WIDTH = 12,
		parameter int DATA_WIDTH = 32 )
	(	input logic clk, reset,
		Ram_if.client mem,
		Jtag_if.user jtag );

logic we;
logic[0 : ADDR_WIDTH-1] addr;  // reversed boundaries are intentional
logic[0 : DATA_WIDTH-1] data;  // due to JTAG shift direction

logic update, update_d;

assign jtag.tdo = data[DATA_WIDTH-1];


//---------------------------------------------------------------------------
/** Shift address and data from JTAG TDI pin */
always_ff @(posedge jtag.tck or posedge jtag.treset)
begin
	if( jtag.treset ) begin
		we <= 1'b0;
		addr <= '0;
		data <= '0;
	end else begin
		if( jtag.sel ) begin
			// read on JTAG capture
			if( jtag.capture )
				data <= mem.data_r;

			// shift new address and data in SHIFT-DR
			if( jtag.shift ) begin
				we <= jtag.tdi;
				addr[0] <= we;
				for(int i=ADDR_WIDTH-1; i>0; i--)
					addr[i] <= addr[i-1];

				data[0] <= addr[ADDR_WIDTH-1];
				for(int i=DATA_WIDTH-1; i>0; i--)
					data[i] <= data[i-1];
			end
		end
	end
end
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// synchronizer logic with configurable number of synchronizer flip-flops.
// (The JTAG interface is asynchronous to clk)
generate
	logic update_stages[0 : NUM_SYNC_STAGES-1];

	always_ff @(posedge clk)
		if( reset )
			update_stages[0] <= 1'b0;
		else
			update_stages[0] <= jtag.sel & jtag.update;

	genvar i;
	for(i=1; i<NUM_SYNC_STAGES; i++) begin : sync_ff
		always_ff @(posedge clk)
			if( reset )
				update_stages[i] <= 1'b0;
			else
				update_stages[i] <= update_stages[i-1];
	end : sync_ff

	assign update = update_stages[NUM_SYNC_STAGES-1];
endgenerate
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
/** Delay update signal for edge detection */
always_ff @(posedge clk)
	if( reset )
		update_d <= 1'b0;
	else
		update_d <= update;
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
/** Execute memory access */
always_ff @(posedge clk)
begin
	if( reset ) begin
		mem.addr <= '0;
		mem.data_w <= '0;
		mem.we <= 1'b0;
		mem.be <= '1;
		mem.en <= 1'b0;
	end else begin
		// write on edge of update
		if( update & ~update_d ) begin
			mem.addr <= addr;
			mem.data_w <= data;
			mem.we <= we;
			mem.be <= '1;
			mem.en <= 1'b1;
		end else begin
			//mem.addr <= '0;
			//mem.data_w <= '0;
			mem.we <= 1'b0;
			mem.be <= '1;
			mem.en <= 1'b0;
		end
	end
end
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Embedded assertions
//---------------------------------------------------------------------------
// synopsys translate_off
/* mem.data_r must not change, when the ram is disabled */
//check_ram_disabled_keeps_output: assert property(
	//@(posedge clk) disable iff(reset)
		//mem.en == 1'b0 |=> $stable(mem.data_r)
	//);
// synopsys translate_on
//---------------------------------------------------------------------------

endmodule

// vim: noexpandtab ts=4 sw=4 softtabstop=0 nosmarttab:
