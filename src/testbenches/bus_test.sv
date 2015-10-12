/** _use_m4_ include(bus.m4) */

// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Constraint random testing of Bus_if trees */
module Bus_test();
  localparam time clk_period = 10ns;
  localparam int ADDR_WIDTH = 32;
  localparam int DATA_WIDTH = 32;
  localparam real REQ_RATE = 0.1;
  localparam int RAND_TEST_MAX = 10000;
  localparam int RAND_TEST_CMP = int'(REQ_RATE * real'(RAND_TEST_MAX));


  `include "ram_transactor.sv"

  logic clk, reset;

  //---------------------------------------------------------------------------
  // Design under test
  //---------------------------------------------------------------------------

  Bus_if #(.byteen(1'b1)) bus_master_a(.Clk(clk)),
                          bus_master_b(.Clk(clk)),
                          bus_master_c(.Clk(clk)),
                          bus_master_bc(.Clk(clk));
                          //bus_master(.Clk(clk)),
                          //bus_master_d(.Clk(clk)),
                          //bus_split_0_if(.Clk(clk)),
                          //bus_split_1_if(.Clk(clk)),
                          //bus_slave_0(.Clk(clk)),
                          //bus_slave_1(.Clk(clk)),
                          //bus_slave_2(.Clk(clk)),
                          //bus_slave_2_d(.Clk(clk)),
                          //bus_slave_2_d2(.Clk(clk)),
                          //bus_slave_3(.Clk(clk));
                          //bus_slave_3_d(.Clk(clk));

  Ram_if #(.ADDR_WIDTH(32), .DATA_WIDTH(32)) cache_read_if();
  Ram_if #(.ADDR_WIDTH(10), .DATA_WIDTH(32)) cache_store_r(),
                                             cache_store_w();

  bus_begin(testbus, clk, <:.byteen(1):>)
    master(bus_master_a) 
    master(bus_master_b)
    master(bus_master_c) arb arb
        delay
        split(29)
          split(28)
            slave(0)
            slave(1)
          split(28)
            delay slave(2_d2)
            slave(3)
  bus_end()

  /*Bus_if_arb #(
    .RESET_BY_0(1'b0)
  ) master_arb_bc (
    .in_0(bus_master_b),
    .in_1(bus_master_c),
    .out(bus_master_bc)
  );

  Bus_if_arb #(
    .RESET_BY_0(1'b0)
  ) master_arb (
    .in_0(bus_master_a),
    .in_1(bus_master_bc),
    .out(bus_master)
  );

  Bus_delay delay_master(
    .in(bus_master),
    .out(bus_master_d)
  );

  Bus_if_split #(29) bus_split_root(
    .top(bus_master_d),
    .out_0(bus_split_0_if),
    .out_1(bus_split_1_if)
  );

  Bus_if_split #(28) bus_split_0(
    .top(bus_split_0_if),
    .out_0(bus_slave_0),
    .out_1(bus_slave_1)
  );

  Bus_if_split #(28) bus_split_1(
    .top(bus_split_1_if),
    .out_0(bus_slave_2),
    .out_1(bus_slave_3)
  );*/
  
  //Iobus_dummy #(
    //.RD_ACCEPT_LATENCY(0),
    //.WR_ACCEPT_LATENCY(0),
    //.RD_RETURN_LATENCY(1),
    //.WR_RETURN_LATENCY(1),
    //.RESPONSE_FUNCTION(1),  // memory
    //.BYTE_ENABLED(1'b1)
  //) slave_0 (
    ////.clk(bus_split_0_if.Clk),
    ////.reset(~bus_split_0_if.MReset_n),
    ////.iobus(bus_split_0_if)
    //.clk(bus_slave_0.Clk),
    //.reset(~bus_slave_0.MReset_n),
    //.iobus(bus_slave_0)
    ////.clk(bus_master_d.Clk),
    ////.reset(~bus_master_d.MReset_n),
    ////.iobus(bus_master_d)
  //);

  Memory_block slave_0_mem (.bus(testbus_slave_0));


  Iobus_dummy #(
    .RD_ACCEPT_LATENCY(0),
    .WR_ACCEPT_LATENCY(0),
    .RD_RETURN_LATENCY(1),
    .WR_RETURN_LATENCY(1),
    .RESPONSE_FUNCTION(1),  // memory
    .BYTE_ENABLED(1'b1)
  ) slave_1 (
    .clk(testbus_slave_1.Clk),
    .reset(~testbus_slave_1.MReset_n),
    //.iobus(bus_slave_1)
    .iobus(testbus_slave_1)
    //.clk(bus_split_1_if.Clk),
    //.reset(~bus_split_1_if.MReset_n),
    //.iobus(bus_split_1_if)
  );
 
  //Bus_delay delay_slave_2_0(bus_slave_2, bus_slave_2_d);
  //Bus_delay delay_slave_2_1(bus_slave_2, bus_slave_2_d2);

  Iobus_dummy #(
    .RD_ACCEPT_LATENCY(0),
    .WR_ACCEPT_LATENCY(0),
    .RD_RETURN_LATENCY(1),
    .WR_RETURN_LATENCY(1),
    .RESPONSE_FUNCTION(1),  // memory
    .BYTE_ENABLED(1'b1)
  ) slave_2 (
    .clk(testbus_slave_2_d2.Clk),
    .reset(~testbus_slave_2_d2.MReset_n),
    .iobus(testbus_slave_2_d2)
    //.clk(bus_slave_2.Clk),
    //.reset(~bus_slave_2.MReset_n),
    //.iobus(bus_slave_2)
  );
 
  //Bus_delay delay_slave_3(bus_slave_3, bus_slave_3_d);

  Iobus_dummy #(
    .RD_ACCEPT_LATENCY(0),
    .WR_ACCEPT_LATENCY(0),
    .RD_RETURN_LATENCY(1),
    .WR_RETURN_LATENCY(1),
    .RESPONSE_FUNCTION(1),  // memory
    .BYTE_ENABLED(1'b1)
  ) slave_3 (
    //.clk(bus_slave_3_d.Clk),
    //.reset(~bus_slave_3_d.MReset_n),
    //.iobus(bus_slave_3_d)
    .clk(testbus_slave_3.Clk),
    .reset(~testbus_slave_3.MReset_n),
    .iobus(testbus_slave_3)
  );

  assign bus_master_a.MReset_n = ~reset;
  assign bus_master_b.MReset_n = ~reset;


  // cache
  Read_cache #(
    .INDEX_SIZE(6),
    .DISPLACEMENT_SIZE(4),
    .TAG_SIZE(32 - 10),
    .WORD_SIZE(32)
  ) read_cache (
    .clk,
    .reset,
    .fetch_bus(bus_master_c),
    .read_bus(cache_read_if),
    .store_r(cache_store_r),
    .store_w(cache_store_w)
  );

  L1_memory #(
    .ADDR_WIDTH(10),
    .DATA_WIDTH(32),
    .IS_DUALPORT(1'b1)
  ) cache_store (
    .clk,
    .reset,
    .intf(cache_store_r),
    .intf2(cache_store_w)
  );

  //---------------------------------------------------------------------------
  // Clock generation
  //---------------------------------------------------------------------------
  
  always #(clk_period/2) clk = ~clk;


  //---------------------------------------------------------------------------
  // Test control
  //---------------------------------------------------------------------------
  

  typedef logic[DATA_WIDTH-1:0] Data;
  typedef logic[ADDR_WIDTH-1:0] Addr;

  task automatic rw_test(input Addr from, to, ref Bus_tb::Bus_transactor #(Addr, Data) trans);
    Data data[] = new [to - from +1];
    Data data_r;

    for(Addr i=from; i<=to; i++) begin
      data[i-from] = $urandom;
      trans.write(i, data[i-from], '1);
    end

    for(Addr i=from; i<=to; i++) begin
      trans.read(i, '1, data_r);
      check_rw_test: assert(data_r == data[i-from])
      else
        $error("read/write test failed at address 0x%08h (expected=0x%08h, got=0x%08h)",
          i, data[i-from], data_r);
    end
  endtask

  task automatic rw_odd_even_test(
      input Addr from, to, bit even, int count, real rate,
      ref Bus_tb::Bus_transactor #(Addr, Data) trans);

    for(int i=0; i<count; i++) begin
      Data data_w;
      Data data_r;
      Addr addr;

      data_w = $urandom;
      addr = $urandom_range(to, from);
      addr[0] = even;

      trans.write(addr, data_w, '1);
      while( $urandom_range(RAND_TEST_MAX) > int'(rate * real'(RAND_TEST_MAX)) ) @(posedge clk);
      trans.read(addr, '1, data_r);
      while( $urandom_range(RAND_TEST_MAX) > int'(rate * real'(RAND_TEST_MAX)) ) @(posedge clk);

      check_odd_even_test: assert(data_r == data_w)
      else
        $error("odd/even test failed at address 0x%08h (expected=0x%08h, got=0x%08h)",
          addr, data_w, data_r);
    end
  endtask

  task automatic cache_test(
      input Addr from, to, int count, length_min, length_max,
      ref Bus_tb::Bus_transactor #(Addr, Data) trans_w,
      ref Ram_transactor #(Addr, Data) trans_r);
   
    Addr addr;
    int length;
    Data data[];
    Data data_r;

    $display("allocating %0d words for cache test", (to-from+1));
    data = new [to - from +1];

    for(Addr i=from; i<=to; i++) begin
      //data[i-from] = $urandom;
      data[i-from] = i;
      trans_w.write(i, data[i-from], '1);
    end

    @(negedge clk);
    for(int i=0; i<count; i++) begin
      length = $urandom_range(length_max, length_min);
      addr = $urandom_range(to - length, from);

      for(int j=addr; j<addr+length; j++) begin
        trans_r.read(j, '1, data_r);
        check_cache_test: assert(data_r == data[j-from])
        else
          $error("cache test failed at address 0x%08h (expected=0x%08h, got=0x%08h)",
          addr, data[j-from], data_r);
      end
    end
    @(posedge clk);
  endtask

  initial begin
    Bus_tb::Bus_transactor #(Addr, Data) trans_a, trans_b;
    Ram_transactor #(Addr, Data) trans_cache;
    Data data_r;

    clk = 1'b0;
    reset = 1'b1;

    #(100ns) reset = 1'b0;

    trans_a = new (bus_master_a);
    trans_b = new (bus_master_b);
    trans_cache = new (cache_read_if, clk_period);
   
    $display("read/write...");
    @(posedge clk);
    fork
      rw_test(32'h0000_0000, 32'h0000_1000, trans_a);
      rw_test(32'h1000_0000, 32'h1000_1000, trans_b);
    join

    $display("odd/even test...");
    fork
      rw_odd_even_test(32'h0000_0000, 32'h0000_1000 /*32'h3fff_ffff*/, 1'b0, 100000, 0.5, trans_a);
      rw_odd_even_test(32'h0000_0000, 32'h0000_1000 /*32'h3fff_ffff*/, 1'b1, 100000, 0.5, trans_b);
    join

    $display("random test...");
    for(int i=0; i<10000; i++) begin
      fork
        begin
          @(posedge clk);
          if( $urandom_range(RAND_TEST_MAX) < RAND_TEST_CMP ) begin
            Data data_w;
            data_w = $random;
            trans_a.write(0, data_w, 4'hf);
            trans_a.read(0, 4'hf, data_r);
            assert(data_r == data_w);
          end
        end

        begin
          @(posedge clk);
          if( $urandom_range(RAND_TEST_MAX) < RAND_TEST_CMP ) begin
            Data data_w;
            data_w = $random;
            trans_b.write(1, data_w, 4'hf);
            trans_b.read(1, 4'hf, data_r);
            assert(data_r == data_w);
          end
        end
      join
    end

    $display("cache test...");
    forever begin
      fork
        rw_odd_even_test(32'h1000_0000, 32'h1fff_ffff, 1'b0, 100000, 0.5, trans_a);
        cache_test(32'h0000_0000, 32'h0000_1fff, 10000, 1, 40, trans_b, trans_cache);
      join
    end

    $display("all tests done.");
    $stop;
  end

endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
