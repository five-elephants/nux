// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module Ram_delay
	#(	parameter int NUM_STAGES = 3,
		parameter int ADDR_WIDTH = 10,   // number of address bits
		              DATA_WIDTH = 32 ) // number of data bits per address
	(	input logic clk, reset,
		Ram_if.memory  mem,
		Ram_if.client  client 
	);

//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

localparam integer BYTE_COUNT = DATA_WIDTH/8;

typedef struct {
	logic en;
	logic[ADDR_WIDTH-1:0] addr;
	logic[DATA_WIDTH-1:0] data_w;
	logic we;
	logic[BYTE_COUNT-1:0] be;
} Pkt_to_mem;

typedef struct {
	logic[DATA_WIDTH-1:0] data_r;
} Pkt_from_mem;


enum logic[0:0] {
	S_IDLE   = 1'b0,
	S_ACTIVE = 1'b1,
	S_UNDEF  = 1'bx
} state;

logic[3:0]    ctr, next_ctr;
Pkt_to_mem    to_mem[0:NUM_STAGES];
Pkt_from_mem  from_mem[0:NUM_STAGES];
Pkt_to_mem    next_to_mem;
Pkt_from_mem  next_from_mem;

//---------------------------------------------------------------------------
// FSM
//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
	if( reset )
		state <= S_IDLE;
	else
		unique case(state)
			S_IDLE: begin
				if( client.en )
					state <= S_ACTIVE;
			end

			S_ACTIVE: begin
				if( ctr == 0 )
					state <= S_IDLE;
			end

			default: begin
				state <= S_UNDEF;
			end
		endcase


always_comb begin
	// default assignment
	next_ctr = ctr;
	next_to_mem.en = 1'b0;
	next_to_mem.addr = '0;
	next_to_mem.data_w = '0;
	next_to_mem.we = 1'b0;
	next_to_mem.be = '0;
	client.data_r = 'x;
	client.delay = 1'b0;

	unique case(state)
		S_IDLE: begin
			next_to_mem.en = client.en;
			next_to_mem.addr = client.addr;
			next_to_mem.data_w = client.data_w;
			next_to_mem.be = client.be;
			next_to_mem.we = client.we;
			client.data_r = from_mem[NUM_STAGES].data_r;

			if( client.en )
				next_ctr = NUM_STAGES;
		end

		S_ACTIVE: begin
			next_ctr = ctr -1;
			client.delay = 1'b1;
		end

		default: begin
			next_ctr = 'x;
			next_to_mem.addr = 'x;
			next_to_mem.data_w = 'x;
			next_to_mem.be = 'x;
			next_to_mem.we = 1'bx;
			client.delay = 1'bx;
		end
	endcase
end

//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
	if( reset )
		ctr <= NUM_STAGES;
	else
		ctr <= next_ctr;

always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		for(int i=0; i<=NUM_STAGES; i++) begin
			to_mem[i].addr <= '0;
			to_mem[i].we <= 1'b0;
			to_mem[i].data_w <= 1'b0;
			to_mem[i].be <= '0;
			from_mem[i].data_r <= '0;
		end
	end else begin
		to_mem[0] <= next_to_mem;
		from_mem[0] <= next_from_mem;

		for(int i=1; i<=NUM_STAGES; i++) begin
			to_mem[i] <= to_mem[i-1];
			from_mem[i] <= from_mem[i-1];
		end
	end


assign
	mem.addr = to_mem[NUM_STAGES].addr,
	mem.data_w = to_mem[NUM_STAGES].data_w,
	mem.be = to_mem[NUM_STAGES].be,
	mem.we = to_mem[NUM_STAGES].we,
	mem.en = to_mem[NUM_STAGES].en;

assign
	next_from_mem.data_r = mem.data_r;

endmodule
