// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Level-1 memory 
 *
 * Synchronous memory with byte-enable. Inferred as BlockRAM on Xilinx FPGAs.
 * If IS_DUALPORT is set, intf2 is a valid interface with same address and
 * data width as intf. Write-collisions are resolved: intf2 has priority over
 * intf.
 *
 * Synthesis results using Synopsys Synplify are not optimal:
 * - When IS_DUALPORT = 1'b0 everything is fine. Synplify generates one ram
 *   component for every memory bank. They are later packed into one RAMB36
 *   by the placer.
 * - When IS_DUALPORT = 1'b1 the result is still functionally correct, but
 *   Synplify infers 8 nram components. They are packed into 4 RAMB18. Two
 *   RAMB18 are equivalent to one RAMB36, so this doubles resource utilization.
 *   The byte-enable RAM generated using the SynCORE wizard from Synplify
 *   delivers the same result.
 * */
module L1_memory
	#(	parameter integer  ADDR_WIDTH = 10,
		                   DATA_WIDTH = 32,
		parameter bit      IS_DUALPORT = 1'b1 )

	(	input logic    clk,
		               reset,

		Ram_if.memory  intf,
		Ram_if.memory  intf2 );
	
	localparam MEM_SIZE = 2**ADDR_WIDTH;
	localparam integer BYTE_COUNT = DATA_WIDTH/8 + ((DATA_WIDTH%8 ==0) ? 0 : 1);

// 	logic[DATA_WIDTH-1:0] mem[0:MEM_SIZE-1];  /* synthesis synramstyle = "no_rw_check" */
// 
// 	always_ff @(posedge clk)
// 	begin : read_mem
// 		if( reset )
// 			intf.data_r <= '0;
// 		else begin
// 			if( intf.en )
// 				intf.data_r <= mem[intf.addr];
// 		end
// 	end : read_mem
// 	
// 	always_ff @(posedge clk)
// 	begin : read_mem_b
// 		if( reset )
// 			intf2.data_r <= '0;
// 		else begin
// 			if( intf2.en )
// 				intf2.data_r <= mem[intf2.addr];
// 		end
// 	end : read_mem_b
// 
// 
// 	generate
// 		genvar by;
// 		for(by=0; by<BYTE_COUNT; by++) begin : bank
// 			//---------------------------------------------------------------------------
// 			always @(posedge clk)
// 			begin
// 				if( intf.en ) begin : port_enable
// 					if( intf.we && intf.be[by] ) begin : write_enable
// 						mem[intf.addr][8*(by+1)-1 -: 8] <= intf.data_w[8*(by+1)-1 -: 8];
// 					end : write_enable
// 				end : port_enable
// 				
// 				if( intf2.en ) begin : port_b_enable
// 					if( intf2.we && intf2.be[by] )
// 						mem[intf2.addr][8*(by+1)-1 -: 8] <= intf2.data_w[8*(by+1)-1 -: 8];
// 				end : port_b_enable
// 			end
// 			//---------------------------------------------------------------------------
// 		end : bank
// 	endgenerate

	//---------------------------------------------------------------------------
// 	generate if( IS_DUALPORT ) begin : port_b
// 		always @(posedge clk)
// 		begin
// 			if( reset ) begin
// 				intf2.data_r <= '0;
// 			end else begin
// 				if( intf2.en ) begin : port_enable
// 					intf2.data_r <= mem[intf2.addr];
// 					
//  					if( intf2.we ) begin : write_enable
//  						mem[intf2.addr] <= intf2.data_w; 						
//  					end : write_enable
// 				end : port_enable
// 			end
// 		end
// 	end : port_b
// 	endgenerate
	//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
//---------------------------------------------------------------------------
//---------------------------------------------------------------------------
// synopsys translate_off

	logic[7:0] data_r[0:BYTE_COUNT-1];
	logic[7:0] data_r2[0:BYTE_COUNT-1];

	generate
		genvar i;
		for(i=0; i<BYTE_COUNT; ++i) begin : bank
			logic[7:0] mem[0:MEM_SIZE-1];
			//logic[7:0] data_r;
			logic[7:0] data_w;

			wire we;
			
			logic[7:0] data_w2;
			wire we2;

			assign we = intf.we & intf.be[i];

			/** Generate byte-sized write data signals */
			always_comb
				for(int b=0; b<8; b++) begin
					//intf.data_r[i*8+b] = data_r[b];
					data_w[b] = intf.data_w[i*8+b];
				end

			/** Read/write process for one byte */
			always @(posedge clk)
			begin : rw_proc
				if( reset ) begin
					data_r[i] <= 8'b0;
				end else begin
					if( intf.en ) begin
						data_r[i] <= mem[intf.addr];

						if( we )
							mem[intf.addr] <= data_w;
					end

					// doing the write of the second port here resolves
					// write collisions
					if( IS_DUALPORT ) begin : dual_port
						if( intf2.en ) begin
							data_r2[i] <= mem[intf2.addr];

							if( we2 )
								mem[intf2.addr] <= data_w2;
						end
					end : dual_port
				end
			end : rw_proc

			//
			// second port
			//
			if( IS_DUALPORT == 1'b1 ) begin : dual_port
				assign we2 = intf2.we & intf2.be[i];

				always_comb
					for(int b=0; b<8; b++) begin
						data_w2[b] = intf2.data_w[i*8+b];
					end
					
				// doing the write here will lead to undeterministic behaviour
				// for write-collisions. Also you need to add 
				// syn_ramstyle = "no_rw_check" to mem.
// 				always @(posedge clk)
// 				begin
// 					if( reset )
// 						data_r2[i] <= 8'b0;
// 					else begin
// 						if( intf2.en ) begin
// 							data_r2[i] <= mem[intf2.addr];
// 							
// 							if( we2 )
// 								mem[intf2.addr] <= data_w2;
// 						end
// 					end
// 				end

			end : dual_port

		end


		if( IS_DUALPORT == 1'b1 ) begin : write_data_r2
			/** reduce byte-size data_r from generate block to word-size data_r from
			 * the interface */
			always_comb
				for(int by=0; by<BYTE_COUNT; by++)
					for(int bi=0; bi<8; bi++)
						intf2.data_r[by*8+bi] = data_r2[by][bi];
		end : write_data_r2
	endgenerate

	/** reduce byte-size data_r from generate block to word-size data_r from
	 * the interface */
	always_comb
		for(int by=0; by<BYTE_COUNT; by++)
			for(int bi=0; bi<8; bi++)
				intf.data_r[by*8+bi] = data_r[by][bi];


	assign 
		intf.delay = 1'b0,
		intf2.delay = 1'b0;

// synopsys translate_on
endmodule
