// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Test_read_cache();

  localparam time clk_period = 10ns;

  localparam int INDEX_SIZE = 4;
  localparam int DISPLACEMENT_SIZE = 6;
  localparam int TAG_SIZE = 32 - (INDEX_SIZE + DISPLACEMENT_SIZE);
  localparam int WORD_SIZE = 32;
  localparam int MEM_SIZE = 2**32;

  logic clk, reset;


  //---------------------------------------------------------------------------
  // Design under test
  //---------------------------------------------------------------------------

  Bus_if #(
    .byteen(1'b1)
  ) fetch_bus(.Clk(clk));
  Ram_if read_bus();
  Ram_if store_r();
  Ram_if store_w();

  Read_cache #(
    .INDEX_SIZE(INDEX_SIZE),
    .DISPLACEMENT_SIZE(DISPLACEMENT_SIZE),
    .TAG_SIZE(TAG_SIZE),
    .WORD_SIZE(WORD_SIZE)
  ) uut (
    .clk, .reset,

    .fetch_bus(fetch_bus),
    .read_bus(read_bus),
    
    .store_r(store_r),
    .store_w(store_w)
  );


  //---------------------------------------------------------------------------
  // Test environment
  //---------------------------------------------------------------------------
  
  L1_memory #(
    .ADDR_WIDTH(INDEX_SIZE+DISPLACEMENT_SIZE),
    .DATA_WIDTH(32),
    .IS_DUALPORT(1'b1)
  ) cache_store (
    .clk, .reset,
    .intf(store_r),
    .intf2(store_w)
  );

  Iobus_dummy #(
    .RESPONSE_FUNCTION(3)  // return address
  ) mem (
    .clk, .reset,
    .iobus(fetch_bus)
  );

  //---------------------------------------------------------------------------
  // Clock generation
  //---------------------------------------------------------------------------
  
  always #(clk_period/2) clk = ~clk;


  //---------------------------------------------------------------------------
  // Stimulus generation
  //---------------------------------------------------------------------------
 
  //---------------------------------------------------------------------------
  task inst_fetch(virtual Ram_if ram, input int addr, output logic[31:0] result);
    ram.en = 1'b1;
    ram.we = 1'b0;
    ram.be = '1;
    ram.addr = addr;
    ram.data_w = '0;

    do begin
      #(clk_period);
    end while( ram.delay );

    result = ram.data_r;
  endtask

  function automatic bit check_result(input int addr, logic[31:0] result);
    return (result == addr);
  endfunction

  //---------------------------------------------------------------------------

  initial begin
    logic[31:0] res;
    int addr;
    const int jump_prob = (2**31 -1) / 40;

    clk = 1'b0;
    reset = 1'b1;

    #(100ns);
    @(negedge clk) reset = 1'b0;

    $display("Starting linear fetch test");
    for(int i=0; i<1000; i++) begin
      inst_fetch(read_bus, i, res);
      check_linear_fetch_result: assert(check_result(i, res))
      else
        $error("linear fetch failed at %08x", i);
      //$display("for %08h fetched = %08h", i, res);
    end

    $display("Starting random fetch test");
    for(int i=0; i<1000; i++) begin
      addr = $urandom;
      inst_fetch(read_bus, addr, res);
      check_random_fetch_result: assert(check_result(addr, res))
      else
          $error("random fetch failed at %08x", addr);
    end

    $display("Starting combined linear/random test");
    for(int i=0; i<1000; i++) begin
      if( $urandom < jump_prob )
        addr = $urandom;
      else
        addr = addr + 1;

      inst_fetch(read_bus, addr, res);
      check_linear_random_fetch_result: assert(check_result(addr, res))
      else
          $error("combined linear/random fetch failed at %08x", addr);
    end

    $stop;
  end
endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
