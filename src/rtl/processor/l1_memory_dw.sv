// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module L1_memory_dw
  #(parameter integer  ADDR_WIDTH = 10,
                       DATA_WIDTH = 32,
    parameter bit      IS_DUALPORT = 1'b1 )

  (input logic    clk,
                  reset,

   Ram_if.memory  intf);

	localparam MEM_SIZE = 2**ADDR_WIDTH;
	localparam integer BYTE_COUNT = DATA_WIDTH/8;

	logic[DATA_WIDTH-1 : 0] mem[0 : MEM_SIZE-1];  /* synthesis syn_keep = 1 */

	logic[BYTE_COUNT-1 : 0] we;
	logic[DATA_WIDTH-1 : 0] w;
//	logic[7:0]              bytes[0 : BYTE_COUNT-1];

	logic                   delay;


	//assign intf.delay = 1'b0;

	//---------------------------------------------------------------------------
	/** generate local byte-wise write enable signals */
	always_comb
		for(int i=0; i<BYTE_COUNT; i++) begin
			we[i] = intf.we & intf.be[i];
		end
	//---------------------------------------------------------------------------
	/** select input to mem from mem or data input, depending on byte-wise
	 * write enable. (Loosely based on XST coding style for RAM with 
	 * byte-enable) */
	always_comb
	begin : sel_input
		for(int i=0; i<BYTE_COUNT; i++) begin
			if( we[i] == 1'b1 )
				for(int j=0; j<8; j++) w[i*8+j] = intf.data_w[i*8+j];
			else
				for(int j=0; j<8; j++) w[i*8+j] = mem[intf.addr][i*8+j];
		end
	end : sel_input
	//---------------------------------------------------------------------------
	/** Perform read and write data access */
	always_ff @(posedge clk)
	begin
		if( reset ) begin
			intf.data_r <= '0;
		end else begin
			if( intf.en ) begin
				if( delay )
					intf.data_r <= 'x;
				else
					intf.data_r <= mem[ intf.addr ];

				if( intf.we )
					mem[ intf.addr ] <= w;
			end
		end
	end
  //---------------------------------------------------------------------------

  assign intf.delay = 1'b0;

endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
