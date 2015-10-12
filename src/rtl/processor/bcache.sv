// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module Bcache
	#(parameter int lookup_width = 8,
		parameter int addr_width = 12 )
	( input logic                  clk, reset,
		input logic[addr_width-1:0]  addr,

		input logic                  jump,
		input logic[addr_width-1:0]  jump_vec,

		input logic                  taken,
		input logic                  not_taken,
		input logic[addr_width-1:0]  pc,

		output logic                 predict_taken,
		output logic[addr_width-1:0] predict_target );

//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

localparam int table_size = 2**lookup_width;
localparam int tag_width = (addr_width <= lookup_width) ? 1 : (addr_width-lookup_width);

typedef logic[lookup_width-1:0] Index;
typedef logic[tag_width-1:0] Tag;
typedef logic[1:0] Counter;
typedef logic[addr_width-1:0] Target;


logic valids[0:table_size-1];
Counter counts[0:table_size-1];
Target targets[0:table_size-1];
Tag tags[0:table_size-1];
Index index_addr;
Index index_pc;
Tag tag_addr;
Tag tag_pc;

//---------------------------------------------------------------------------
// Logic
//---------------------------------------------------------------------------

function automatic Index make_index(input logic[addr_width-1:0] addr);
	return addr[$left(Index):$right(Index)];
endfunction

function automatic Tag make_tag(input logic[addr_width-1:0] addr);
	if( addr_width == lookup_width )
		return '0;
	else
		return addr[$left(Index)+$left(Tag)+1 : $left(Index)+$right(Tag)+1];
endfunction

function automatic Counter count_sat_inc(input Counter c);
	if( c == 2'b11 )
		return c;
	else
		return c + 1;
endfunction

function automatic Counter count_sat_dec(input Counter c);
	if( c == 2'b00)
		return c;
	else
		return c - 1;
endfunction

/** Index generation */
assign index_addr = make_index(addr);
assign index_pc = make_index(pc);
assign tag_addr = make_tag(addr);
assign tag_pc = make_tag(pc);


/** Cache readout process */
always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		predict_taken <= 1'b0;
		predict_target <= 'b0;
	end else begin
		if( valids[index_addr] && (tag_addr == tags[index_addr]) )
			predict_taken <= counts[index_addr][1];
		else
			predict_taken <= 1'b0;

		predict_target <= targets[index_addr];
	end


/** Counting process */
always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		for(int i=0; i<table_size; i++) begin
			valids[i] <= 1'b0;
			counts[i] <= 2'b11;
			tags[i] <= '0;
		end
	end	else begin
		if( taken || not_taken ) begin
			if( tag_pc == tags[index_pc] ) begin
				if( taken ) begin
					counts[index_pc] <= count_sat_inc(counts[index_pc]);
				end

				if( not_taken ) begin
					counts[index_pc] <= count_sat_dec(counts[index_pc]);
				end

				valids[index_pc] <= 1'b1;
			end else begin
				if( taken ) begin
					counts[index_pc] <= count_sat_inc(2'b11);
				end

				if( not_taken ) begin
					counts[index_pc] <= count_sat_dec(2'b11);
				end

				valids[index_pc] <= 1'b1;
				tags[index_pc] <= tag_pc;
			end
		end
	end

always_ff @(posedge clk)
begin
	if( taken )
		targets[index_pc] <= jump_vec;
	else if( not_taken )
		targets[index_pc] <= addr+1;
end


`ifndef SYNTHESIS
	initial begin
		check_static_lookup_width: assert(lookup_width <= addr_width)
			else $error("The branch cache may not be larger than the instruction memory");
	end
`endif  /* SYNTHESIS */

endmodule

/* vim: set noet fenc= ff=unix sts=2 sw=2 ts=2 : */
