// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Trap (
	input logic          clk, reset,

	Trap_ctrl_if.trap    ctrl,
	Trap_data_if.trap    data,
	Int_sched_if.trap    except
);

import Pu_types::*;

logic base_trap;


always_ff @(posedge clk or posedge reset)
	if( reset ) begin
		base_trap <= 1'b0;
	end else begin
		// default assignment
		base_trap <= 1'b0;

		if( ctrl.en ) begin
			if( ctrl.to.lts && (signed'(data.a) < signed'(data.b)) )
				base_trap <= 1'b1;
			
			if( ctrl.to.gts && (signed'(data.a) > signed'(data.b)) )
				base_trap <= 1'b1;

			if( ctrl.to.eq && (data.a == data.b) )
				base_trap <= 1'b1;

			if( ctrl.to.ltu && (data.a < data.b) )
				base_trap <= 1'b1;

			if( ctrl.to.gtu && (data.a > data.b) )
				base_trap <= 1'b1;
		end
	end


assign except.base_trap = base_trap & ctrl.en_int;


endmodule
