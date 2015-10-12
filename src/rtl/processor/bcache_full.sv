// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module Bcache_full
  #(parameter int table_size = 16,
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

typedef logic[addr_width-1:0] Tag;
typedef logic[1:0] Counter;
typedef logic[addr_width-1:0] Target;

logic valids[0:table_size-1];
Tag tags[0:table_size-1];
Counter counters[0:table_size-1];
Target targets[0:table_size-1];


//---------------------------------------------------------------------------
// Functions
//---------------------------------------------------------------------------

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

//---------------------------------------------------------------------------
// Readout
//---------------------------------------------------------------------------

generate
  logic[0:table_size-1] read_found;
  logic[0:table_size-1] pred_taken_par;
  Target pred_target_par[0:table_size-1];
  Target next_pred_target;

  genvar i;
  for(i=0; i<table_size; i++) begin : gen_readout
    
    assign read_found[i] = (valids[i] && (tags[i] == addr));
    assign pred_taken_par[i] = read_found[i] & (counters[i][1]);
    assign pred_target_par[i] = {$bits(Target){read_found[i]}} & targets[i];

  end : gen_readout

  // reduce
  always_comb begin
    next_pred_target = pred_target_par[0];
    for(int k=1; k<table_size; k++)
      next_pred_target = next_pred_target | pred_target_par[k];
  end

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      predict_taken <= 1'b0;
      predict_target <= '0;
    end else begin
      predict_taken <= (| pred_taken_par);
      predict_target <= next_pred_target;
    end
  
  `ifndef SYNTHESIS
    
  check_one_found: assert property(
    @(posedge clk)
    ( $onehot0(read_found) )
  );

  `endif

endgenerate

//---------------------------------------------------------------------------
// Update
//---------------------------------------------------------------------------

generate
  logic[0:table_size-1] up_found;
  logic[0:table_size-1] up_new;
  logic all_used;
  logic[0:table_size-1] next_free;
  logic[0:table_size-1] rand_replace;

  // find cell
  genvar up_i;
  for(up_i=0; up_i<table_size; up_i++) begin : gen_update

    // find matching tags
    assign up_found[up_i] = (valids[up_i] && (tags[up_i] == pc));

    // update counters and targets
    always_ff @(posedge clk or posedge reset)
      if( reset ) begin
        counters[up_i] <= '0;
        targets[up_i] <= '0;
        valids[up_i] <= 1'b0;
      end else begin
        if( taken || not_taken ) begin
          if( up_found[up_i] ) begin
            if( taken ) begin
              counters[up_i] <= count_sat_inc(counters[up_i]);
              targets[up_i] <= jump_vec;
            end

            if( not_taken ) begin
              counters[up_i] <= count_sat_dec(counters[up_i]);
              targets[up_i] <= addr+1;
            end
          end

          if( up_new[up_i] ) begin
            if( taken ) begin
              counters[up_i] <= count_sat_inc(2'b11);
              targets[up_i] <= jump_vec;
            end

            if( not_taken ) begin
              counters[up_i] <= count_sat_dec(2'b11);
              targets[up_i] <= addr+1;
            end

            valids[up_i] <= 1'b1;
            tags[up_i] <= pc;
          end
        end
      end

  end : gen_update

  // select new cell if no match found using random replacement
  always_comb begin
    // default assignment
    up_new = '0;

    if( !(|up_found) ) begin
      up_new = (~{$bits(up_new){all_used}} & next_free) | ({$bits(up_new){all_used}} & rand_replace);
    end
  end

  // find free cells
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      next_free <= { 1'b1, {$bits(next_free)-1{1'b0}} };
      all_used <= 1'b0;
    end else begin
      next_free <= '0;
      all_used <= 1'b1;
      for(int k=0; k<table_size; k++)
        if( !valids[k] )
          all_used <= 1'b0;

      for(int j=0; j<table_size; j++)
        if( !valids[j] ) begin
          next_free[j] <= 1'b1;
          break;
        end
    end

  // select random cell
  always_ff @(posedge clk or posedge reset)
    if( reset )
      rand_replace <= { 1'b1, {$bits(rand_replace)-1{1'b0}} };
    else begin
      rand_replace[0] <= rand_replace[$right(rand_replace)];
      rand_replace[1:$right(rand_replace)] <= rand_replace[0:$right(rand_replace)-1];
    end


  `ifndef SYNTHESIS
  
  check_one_update: assert property(
    @(posedge clk)
    ( $onehot0(up_found) )
  );

  check_one_new: assert property(
    @(posedge clk)
    ( $onehot0(up_new) )
  );

  check_one_rand_replace: assert property(
    @(posedge clk)
    ( $onehot0(rand_replace) )
  );

  `endif
endgenerate

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
