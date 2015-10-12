// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Syn_io_dummy
  ( input logic clk, reset,
    Syn_io_if.syn syn_io);


  always @(posedge clk or posedge reset)
    if( reset ) begin
      syn_io.busy = 1'b0;
      syn_io.syn2client_valid = 1'b0;
      syn_io.syn2client_channel = 1'b0;
      syn_io.syn2client_data = '0;
      syn_io.syn2client_pat_ctr = '0;
    end else begin
      if( syn_io.start ) begin
        syn_io.busy <= 1'b1;
        for(int i=0; i<10; i++)
          @(posedge clk);

        syn_io.syn2client_valid <= 1'b1;
        syn_io.syn2client_data <= {4{32'haffe_affe}};
        @(posedge clk);
        syn_io.syn2client_channel <= 1'b1;
        syn_io.syn2client_data <= {4{32'habcd_0123}};
        @(posedge clk);
        
        syn_io.syn2client_channel <= 1'b0;
        syn_io.busy <= 1'b0;
        syn_io.syn2client_data <= '0;
        syn_io.syn2client_valid <= 1'b0;
      end
    end
  

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
