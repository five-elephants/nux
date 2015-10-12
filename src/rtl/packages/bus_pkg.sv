// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



package Bus;
	typedef enum logic[2:0] {
		IDLE = 3'b000,
		WR   = 3'b001,
		RD   = 3'b010,
		RDEX = 3'b011,
		RDL  = 3'b100,
		WRNP = 3'b101,
		WRC  = 3'b110,
		BCST = 3'b111
	} Ocp_cmd;

	typedef enum logic[1:0] {
		NULL = 2'b00,
		DVA  = 2'b01,
		FAIL = 2'b10,
		ERR  = 2'b11
	} Ocp_resp;

	function automatic int clog2(input int x);
		int rv, y;
		y = 1;
		for(rv=0; y < x; rv++) begin 
			y = y * 2;
		end
		return rv;
		//return $clog2(x);
	endfunction
endpackage


/* vim: set noet fenc= ff=unix sts=0 sw=2 ts=2 : */
