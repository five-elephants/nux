// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Pu_types::*;
import Pu_inst::*;

module Coding_test();

logic[31:0] raw_dt;
logic[0:31] raw_to;
Inst inst;

initial begin
	raw_dt = 'hdead_face;
	raw_to = 'hdead_face;
	inst = raw_dt;

	$display("downto (%h):", raw_dt);
	$display("  d.opcd = %h", inst.d.opcd);
	$display("  d.rt   = %h", inst.d.rt);
	$display("  d.ra   = %h", inst.d.ra);
	$display("  d.d    = %h", inst.d.d);

	inst = raw_to;
	$display("to (%h):", raw_to);
	$display("  d.opcd = %h", inst.d.opcd);
	$display("  d.rt   = %h", inst.d.rt);
	$display("  d.ra   = %h", inst.d.ra);
	$display("  d.d    = %h", inst.d.d);
end

endmodule
