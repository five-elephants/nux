// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Bus_serial_test();
  localparam time clk_period = 10ns;

  localparam int SERIAL_WIDTH = 4;
  localparam int PIPELINE_LENGTH = 0;
  localparam int ADDR_WIDTH = 32;
  localparam int DATA_WIDTH = 32;

  logic clk, reset;

  Bus_if #( .byteen(1) ) in(clk), out(clk);

  Bus_serial #(
    .SERIAL_WIDTH(SERIAL_WIDTH),
    .PIPELINE_LENGTH(PIPELINE_LENGTH),
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH)
  ) uut (
    .in(in),
    .out(out)
  );

  
  Iobus_dummy #(
    .RD_ACCEPT_LATENCY(0),
    .WR_ACCEPT_LATENCY(0),
    .RD_RETURN_LATENCY(1),
    .WR_RETURN_LATENCY(1),
    .RESPONSE_FUNCTION(1)  // work as memory
  ) bus_target (
    .clk, .reset,
    .iobus(out)
  );

  always begin
    clk = 1'b0;
    #(clk_period/2);
    clk = 1'b1;
    #(clk_period/2);
  end
 
  assign 
    in.MReset_n = ~reset;

  //---------------------------------------------------------------------------
  task automatic rw_test(input int from, to, ref Bus_tb::Bus_transactor trans);
    int data[] = new [to - from +1];
    int data_r;

    for(int i=from; i<=to; i++) begin
      data[i-from] = $urandom;
      trans.write(i, data[i-from], '1);
    end

    for(int i=from; i<=to; i++) begin
      trans.read(i, '1, data_r);
      check_rw_test: assert(data_r == data[i-from])
      else
        $error("read/write test failed at address 0x%08h (expected=0x%08h, got=0x%08h)",
          i, data[i-from], data_r);
    end
  endtask

  //---------------------------------------------------------------------------
  Bus_tb::Bus_transactor trans;

  initial begin
    int data_r;

    trans = new (in);

    reset = 1'b1;

    #(100ns);
    @(negedge clk);
    reset = 1'b0;


    trans.write(123, 32'hdead_face, 4'hf);
    trans.read(123, 4'hf, data_r);
    check_simple_rw: assert(data_r == 32'hdead_face) else
      $error("simple read write failed");

    rw_test(0, 128, trans);

    $stop;
  end

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
