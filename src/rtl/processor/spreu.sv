// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** Special purpose register execution unit */
module Spreu
	(	input logic clk, reset,
		
		input Pu_types::Cr_op               cr_op,
		input logic[4:0]                    sel_a,
		input logic[4:0]                    sel_b,
		input logic[4:0]                    sel_t,
		input Pu_types::Register_move       reg_mv,
		input logic[7:0]                    src_cr,

		input Pu_types::Word                a,
		input Pu_types::Condition_register  crin,
		input Pu_types::Word                sprin,
		input Pu_types::Msr                 msrin,

		output Pu_types::Word               res,
		output Pu_types::Condition_register crout,
		output Pu_types::Word               sprout,
		output Pu_types::Msr                msrout );

import Pu_types::*;

//Cr_field            crl_out;
Condition_register  crl_out;
Condition_register  crmask;
Condition_register  ccmv;
Cr_bits             ctg_res;

//---------------------------------------------------------------------------
Cr_logic crl
	(	.op(cr_op),
		.cr_in(crin),
		.sel_a(sel_a),
		.sel_b(sel_b),
		.sel_t(sel_t),

		.cr_out(crl_out) );

//---------------------------------------------------------------------------
always_comb
begin
	crmask = '0;

	/*case(src_cr)
		8'b10000000: crmask[0] = 4'hf;
		8'b01000000: crmask[1] = 4'hf;
		8'b00100000: crmask[2] = 4'hf;
		8'b00010000: crmask[3] = 4'hf;
		8'b00001000: crmask[4] = 4'hf;
		8'b00000100: crmask[5] = 4'hf;
		8'b00000010: crmask[6] = 4'hf;
		8'b00000001: crmask[7] = 4'hf;
		default:     crmask = '0;
	endcase*/

	for(int i=0; i<8; i++)
		if( src_cr[7-i] == 1'b1 )
			crmask[i] = 4'hf;
		else
			crmask[i] = 4'h0;
end


always_comb
begin
	Cr_field field;

	// default assignments
	ccmv = crin;

	unique case(sel_a[4:2])
		3'b000:  ccmv[sel_t[4:2]] = crin[0];
		3'b001:  ccmv[sel_t[4:2]] = crin[1];
		3'b010:  ccmv[sel_t[4:2]] = crin[2];
		3'b011:  ccmv[sel_t[4:2]] = crin[3];
		3'b100:  ccmv[sel_t[4:2]] = crin[4];
		3'b101:  ccmv[sel_t[4:2]] = crin[5];
		3'b110:  ccmv[sel_t[4:2]] = crin[6];
		3'b111:  ccmv[sel_t[4:2]] = crin[7];
		default: ccmv[sel_t[4:2]] = 4'bx;
	endcase

	//ccmv[sel_t[4:2]] = crin[sel_a[4:2]];
end


always_comb begin
	Cr_bits b_crin, b_crmask, b_a;

	b_crin = crin;
	b_crmask = crmask;

	for(int i=0; i<DWIDTH; i++)
		b_a[i] = a[DWIDTH-1-i];

	ctg_res = b_crin & b_crmask | b_a & ~b_crmask;
	//for(int i=0; i<8; i++)
		//for(int j=0; j<4; j++)
			////ctg_res[i*4+j] = crin[i][j] & crmask[i][j] | a[31 - (i*4+j)] & ~crmask[i][j];
			//ctg_res[i*4+j] = b_crin[i][j];
end

//---------------------------------------------------------------------------
// Output register
//---------------------------------------------------------------------------
//always_ff @(posedge clk or posedge reset)
	//if( reset ) begin
		//res <= '0;
		//crout <= '0;
		//sprout <= '0;
		//msrout <= '0;
	//end else begin
		//res <= '0;
		//crout <= crl_out;
		//sprout <= '0;
		//msrout <= '0;

		//// perform register move operations
		//unique case(reg_mv)
			//Rmv_none: begin
				//res <=  a;
				//crout <= crl_out;
				//sprout <= sprin;
				//msrout <= msrin;
			//end

			//Rmv_gtc: begin
				//res <= a;
				//crout <= a & crmask | crin & ~crmask;
				//sprout <= sprin;
				//msrout <= msrin;
			//end

			//Rmv_ctg: begin
				////res <= crin & crmask | a & ~crmask;
				//res <= ctg_res;
				////for(int i=0; i<DWIDTH; i++) begin
					////res[i] <= ctg_res[i]; 
				////end
				//crout <= crin;
				//sprout <= sprin;
				//msrout <= msrin;
			//end

			//Rmv_ctc: begin
				//res <= a;
				//crout <= ccmv;
				//sprout <= sprin;
				//msrout <= msrin;
			//end

			//Rmv_stg: begin
				//res <= sprin;
				//crout <= crin;
				//sprout <= sprin;
				//msrout <= msrin;
			//end

			//Rmv_gts: begin
				//res <= a;
				//crout <= crin;
				//sprout <= sprin;
				//msrout <= msrin;
			//end

			//Rmv_gtm, Rmv_mtg: begin
				//res <= msrin;
				//crout <= crin;
				//sprout <= sprin;
				//msrout <= a;
			//end

			//default: begin
				//res <= 'x;
				//crout <= 'x;
				//sprout <= 'x;
				//msrout <= 'x;
			//end
		//endcase
	//end


always_comb begin
		res = '0;
		crout = crl_out;
		sprout = '0;
		msrout = '0;

		// perform register move operations
		unique case(reg_mv)
			Rmv_none: begin
				res =  a;
				crout = crl_out;
				sprout = sprin;
				msrout = msrin;
			end

			Rmv_gtc: begin
				res = a;
				crout = a & crmask | crin & ~crmask;
				sprout = sprin;
				msrout = msrin;
			end

			Rmv_ctg: begin
				//res = crin & crmask | a & ~crmask;
				res = ctg_res;
				//for(int i=0; i<DWIDTH; i++) begin
					//res[i] = ctg_res[i]; 
				//end
				crout = crin;
				sprout = sprin;
				msrout = msrin;
			end

			Rmv_ctc: begin
				res = a;
				crout = ccmv;
				sprout = sprin;
				msrout = msrin;
			end

			Rmv_stg: begin
				res = sprin;
				crout = crin;
				sprout = sprin;
				msrout = msrin;
			end

			Rmv_gts: begin
				res = a;
				crout = crin;
				sprout = sprin;
				msrout = msrin;
			end

			Rmv_gtm, Rmv_mtg: begin
				res = msrin;
				crout = crin;
				sprout = sprin;
				msrout = a;
			end

			default: begin
				res = 'x;
				crout = 'x;
				sprout = 'x;
				msrout = 'x;
			end
		endcase
	end
//---------------------------------------------------------------------------

endmodule
