// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef PREDICTOR__
`define PREDICTOR__

`include "state.sv"
`include "instruction.sv"

class Predictor;
	extern virtual function State predict(input Instruction inst, State state);

	extern virtual function void predict_alu_xo(ref Instruction inst,
			State state,
			Fixed_state rv);

	extern virtual function void predict_branch(ref Instruction inst,
			State state,
			Fixed_state rv);
	
	extern virtual function void predict_load_store(ref Instruction inst,
			State state,
			Fixed_state rv);

	extern virtual function void predict_rotate(ref Instruction inst,
			State state,
			Fixed_state rv);

	extern virtual function void predict_gpr_spr_moves(ref Instruction inst,
			State state,
			Fixed_state rv);

	extern virtual function void predict_interrupt_return(ref Instruction inst,
			State state,
			Fixed_state rv);

	extern virtual function void predict_gpr_msr_moves(ref Instruction inst,
			State state,
			Fixed_state rv);

	extern virtual function void predict_trap(ref Instruction inst,
			State state,
			Fixed_state rv);

	extern virtual function void predict_never(ref Instruction inst,
			State state,
			Fixed_state rv);

	extern function logic[31:0] rotl32(input logic[31:0] x, int d);
	extern function logic[31:0] mask(input int mstart, int mend);
	extern function logic       carry_out(input Word a, Word b, Word y);
	
	const logic[31:0] msr_mask = 32'h00029230;  // bits changeable in MSR are set in the mask
	const logic[31:0] esr_mask = 32'h0f8f07e2;  // bits changeable in ESR are set in the mask
endclass

//---------------------------------------------------------------------------
function State
Predictor::predict(input Instruction inst, State state);
	Inst op;
	Word intermed;
	Cr_field intermed_cr;
	Mem_model mm;
	Fixed_state rv;
	Word xer_word;
	Word a;
	Word res;
	Xer xer;

	mm = state.get_mem_model();
	rv = new(mm.get_mem_size());
	xer_word = state.get_xer();
	xer = xer_word[31:29];

	rv.copy_from(state);
	op = inst.get();
	a = state.get_gpr(op.d.ra);

	intermed_cr.eq = 1'b0;
	intermed_cr.gt = 1'b0;
	intermed_cr.lt = 1'b0;
	intermed_cr.ov = 1'b0;

	rv.set_pc(state.get_pc() +1);

	case(op.d.opcd)
		Op_twi: begin
			predict_trap(inst, state, rv);
		end

		Op_addi: begin
			if( op.d.ra == 0 )
				rv.set_gpr(op.d.rt, { {16{op.d.d[15]}}, op.d.d });
			else
				rv.set_gpr(op.d.rt, 
						state.get_gpr(op.d.ra) + { {16{op.d.d[15]}}, op.d.d });
		end

		Op_addis: begin
			if( op.d.ra == 0 )
				rv.set_gpr(op.d.rt, { op.d.d, {16{1'b0}} });
			else
				rv.set_gpr(op.d.rt, 
						state.get_gpr(op.d.ra) + { op.d.d, {16{1'b0}} });
		end

		Op_addic, Op_addic_rec: begin
			Word res;
			Word ra = state.get_gpr(op.d.ra);
			Cr_field cr = 4'b0;

			{xer.ca, res} = { ra[$left(ra)], ra } + { {17{op.d.d[15]}}, op.d.d };
			res = ra + { {16{op.d.d[15]}}, op.d.d };
			//xer.ca = ra[DWIDTH-1] ^ op.d.d[15] ^ res[DWIDTH-1];
			xer.ca = carry_out(ra, { {17{op.d.d[15]}}, op.d.d }, res);

			rv.set_gpr(op.d.rt, res);
			rv.set_xer({xer, {29{1'b0}}});
		
			if( op.d.opcd == Op_addic_rec ) begin  // record to CR0
				cr.ov = xer.so;
				if( res == 0 )
					cr.eq = 1'b1;
				else begin
					cr.gt = !res[DWIDTH-1];
					cr.lt = res[DWIDTH-1];
				end

				rv.set_cr(0, cr);
			end
		end

		Op_subfic: begin
			Word res;
			Word a;
			Word im;
			Cr_field cr;
			logic cout;

			a = state.get_gpr(op.d.ra);
			im = { {16{op.d.d[15]}}, op.d.d };

			{cout, res} = {im[$left(im)], im} + ~{a[$left(a)], a} + {32'b0, 1'b1};
			//res = im + ~a + 1;
			rv.set_gpr(op.d.rt, res);
			//xer.ca = cout;
			//xer.ca = im[DWIDTH-1] ^ ~a[DWIDTH-1] ^ res[DWIDTH-1];
			xer.ca = carry_out(im, ~a, res);

			rv.set_xer({xer, 29'b0});
		end

		Op_nve_xo: begin
			predict_never(inst, state, rv);
		end

		Op_nvecmpi: begin
			predict_never(inst, state, rv);
		end

		Op_alu_xo: begin
			if( op.xfx.xo == Xop_mtspr || op.xfx.xo == Xop_mfspr )
				predict_gpr_spr_moves(inst, state, rv);
			else if( op.x.xo == Xop_mtmsr || op.x.xo == Xop_mfmsr )
				predict_gpr_msr_moves(inst, state, rv);
			else if( op.x.xo == Xop_tw )
				predict_trap(inst, state, rv);
			else if( op.x.xo == Xop_lwzx
					|| op.x.xo == Xop_lbzx
					|| op.x.xo == Xop_lhzx
					|| op.x.xo == Xop_stwx
					|| op.x.xo == Xop_sthx
					|| op.x.xo == Xop_stbx
					|| op.x.xo == Xop_lwzux
					|| op.x.xo == Xop_lbzux
					|| op.x.xo == Xop_lhzux
					|| op.x.xo == Xop_stwux
					|| op.x.xo == Xop_sthux
					|| op.x.xo == Xop_stbux
					|| op.x.xo == Xop_lhax 
					|| op.x.xo == Xop_lhaux )
				predict_load_store(inst, state, rv);
      else if( op.x.xo == Xop_sync ) begin
      end else
				predict_alu_xo(inst, state, rv);
		end

		Op_andi: begin
			intermed = state.get_gpr(op.d.rt) & { 16'h0000, op.d.d };
			rv.set_gpr(op.d.ra, intermed);

			if( intermed == 0 )
				intermed_cr.eq = 1'b1;
			else begin
				intermed_cr.gt = !intermed[DWIDTH-1];
				intermed_cr.lt = intermed[DWIDTH-1];
			end
		
			intermed_cr.ov = xer.so;

			rv.set_cr(0, intermed_cr);
		end
	
		Op_andis: begin
			intermed = state.get_gpr(op.d.rt) & { op.d.d, 16'h0000 };
			rv.set_gpr(op.d.ra, intermed);

			if( intermed == 0 )
				intermed_cr.eq = 1'b1;
			else begin
				intermed_cr.gt = !intermed[DWIDTH-1];
				intermed_cr.lt = intermed[DWIDTH-1];
			end
		
			intermed_cr.ov = xer.so;

			rv.set_cr(0, intermed_cr);
		end

		Op_ori: begin
			intermed = state.get_gpr(op.d.rt) | { 16'h0000, op.d.d };
			rv.set_gpr(op.d.ra, intermed);
		end

		Op_oris: begin
			intermed = state.get_gpr(op.d.rt) | { op.d.d, 16'h0000 };
			rv.set_gpr(op.d.ra, intermed);
		end

		Op_xori: begin
			intermed = state.get_gpr(op.d.rt) ^ { 16'h0000, op.d.d };
			rv.set_gpr(op.d.ra, intermed);
		end

		Op_xoris: begin
			intermed = state.get_gpr(op.d.rt) ^ { op.d.d, 16'h0000 };
			rv.set_gpr(op.d.ra, intermed);
		end

		Op_branch, Op_bc: begin
			predict_branch(inst, state, rv);
		end

		Op_bclr: begin
			if( op.xl.xo == Xxop_rfi 
				|| op.xl.xo == Xxop_rfci 
				|| op.xl.xo == Xxop_rfmci )
				predict_interrupt_return(inst, state, rv);
			else
				predict_branch(inst, state, rv);
		end

		Op_stw, Op_lwz, Op_stb, Op_lbz, Op_sth, Op_lhz,
		Op_lha, Op_lhau,
		Op_stwu, Op_lwzu, Op_stbu, Op_lbzu, Op_sthu, Op_lhzu,
		Op_lmw, Op_stmw:
		begin
			predict_load_store(inst, state, rv);
		end

		Op_rlwimi, Op_rlwinm, Op_rlwnm: begin
			predict_rotate(inst, state, rv);
		end

		Op_cmpi: begin
			intermed = { {16{op.d.d[15]}}, op.d.d };
			if( a == intermed )
				intermed_cr.eq = 1'b1;
			else if( int'(a) > int'(intermed) )
				intermed_cr.gt = 1'b1;
			else if( int'(a) < int'(intermed) )
				intermed_cr.lt = 1'b1;

			intermed_cr.ov = xer.so;

			rv.set_cr(op.d.rt[4:2], intermed_cr);
		end

		Op_cmpli: begin
			intermed = { 16'h0000, op.d.d };
			if( a == intermed )
				intermed_cr.eq = 1'b1;
			else if( unsigned'(a) > unsigned'(intermed) )
				intermed_cr.gt = 1'b1;
			else if( unsigned'(a) < unsigned'(intermed) )
				intermed_cr.lt = 1'b1;

			intermed_cr.ov = xer.so;

			rv.set_cr(op.d.rt[4:2], intermed_cr);
		end

		Op_mulli: begin
			longint prod64;   // longint is a signed 64bit integer
			longint a64, b64;

			a64 = { {DWIDTH{a[$left(a)]}}, a};
			b64 = { {(DWIDTH+16){op.d.d[$left(op.d.d)]}}, op.d.d};

			prod64 = a64 * b64;
			rv.set_gpr(op.d.rt, (prod64 & 64'h00000000_ffffffff));
			//$display("mult %h * %h = %h", a64, b64, prod64);
		end
	endcase

	return rv;
endfunction
//---------------------------------------------------------------------------
function void 
Predictor::predict_alu_xo(ref Instruction inst, State state, Fixed_state rv);
	Inst op;
	Cr_field cr;
	Word res;
	Xer xer;
	Word xer_word;
	logic cout;
	Word a, b, s;
	logic neg_ov;
	logic[4:0] rot_n;
	logic[31:0] rot_mask;
	bit no_oe = 1'b0;
	bit no_rc = 1'b0;

	op = inst.get();
	cr = '0;
	res = '0;
	cout = 1'b0;
	xer_word = state.get_xer();
	xer = xer_word[31:29];
	a = state.get_gpr(op.xo.ra);
	b = state.get_gpr(op.xo.rb);
	s = state.get_gpr(op.xo.rt);
	
	casez(op.x.xo)
		{1'bz, Xop_neg}: begin
			res = ~a + {{DWIDTH-1{1'b0}}, 1'b1};
			rv.set_gpr(op.xo.rt, res);
			neg_ov = (a[DWIDTH-1] == 1'b1 && a[DWIDTH-2:0] == '0);
		end

		{1'bz, Xop_add}: begin
			{cout, res} = {a[$left(a)], a} + {b[$left(b)], b};
			rv.set_gpr(op.xo.rt, res);
		end

		{1'bz, Xop_addc}: begin
			{cout, res} = {a[$left(a)], a} + {b[$left(b)], b};
			rv.set_gpr(op.xo.rt, res);
			//xer.ca = cout;
			//xer.ca = a[DWIDTH-1] ^ b[DWIDTH-1] ^ res[DWIDTH-1];
			xer.ca = carry_out(a, b, res);
		end

		{1'bz, Xop_adde}: begin
			{cout, res} = {a[$left(a)], a} + {b[$left(b)], b} + {{DWIDTH{1'b0}}, xer.ca};
			rv.set_gpr(op.xo.rt, res);
			//xer.ca = cout;
			//xer.ca = a[DWIDTH-1] ^ b[DWIDTH-1] ^ res[DWIDTH-1];
			xer.ca = carry_out(a, b, res);
		end

		{1'bz, Xop_addme}: begin
			{cout, res} = {a[$left(a)], a} + {{DWIDTH{1'b0}}, xer.ca} + {(DWIDTH+1){1'b1}};
			rv.set_gpr(op.xo.rt, res);
			//xer.ca = cout;
			//xer.ca = a[DWIDTH-1] ^ 1'b1 ^ res[DWIDTH-1];
			xer.ca = carry_out(a, 32'hffffffff, res);
		end

		{1'bz, Xop_addze}: begin
			{cout, res} = {a[$left(a)], a} + {{DWIDTH{1'b0}}, xer.ca};
			rv.set_gpr(op.xo.rt, res);
			//xer.ca = cout;
			//xer.ca = a[DWIDTH-1] ^ res[DWIDTH-1];
			xer.ca = carry_out(a, 32'b0, res);
		end


		{1'bz, Xop_subf}: begin
			{cout, res} = {b[$left(b)], b} + ~{a[$left(a)], a} + {{DWIDTH{1'b0}}, 1'b1};
			rv.set_gpr(op.xo.rt, res);
		end

		{1'bz, Xop_subfc}: begin
			{cout, res} = {b[$left(b)], b} + ~{a[$left(a)], a} + {{DWIDTH{1'b0}}, 1'b1};
			rv.set_gpr(op.xo.rt, res);
			//xer.ca = cout;
			//xer.ca = ~a[DWIDTH-1] ^ b[DWIDTH-1] ^ res[DWIDTH-1];
			xer.ca = carry_out(b, ~a, res);
		end

		{1'bz, Xop_subfe}: begin
			{cout, res} = {b[$left(b)], b} + ~{a[$left(a)], a} + {{DWIDTH{1'b0}}, xer.ca};
			rv.set_gpr(op.xo.rt, res);
			//xer.ca = cout;
			//xer.ca = ~a[DWIDTH-1] ^ b[DWIDTH-1] ^ res[DWIDTH-1];
			xer.ca = carry_out(~a, b, res);
		end

		{1'bz, Xop_subfme}: begin
			{cout, res} = ~{a[$left(a)], a} + {{DWIDTH{1'b0}}, xer.ca} + {(DWIDTH+1){1'b1}};
			rv.set_gpr(op.xo.rt, res);
			//xer.ca = cout;
			//xer.ca = ~a[DWIDTH-1] ^ 1'b1 ^ res[DWIDTH-1];
			xer.ca = carry_out(~a, 32'hffffffff, res);
		end

		{1'bz, Xop_subfze}: begin
			{cout, res} = ~{a[$left(a)], a} + {{DWIDTH{1'b0}}, xer.ca};
			rv.set_gpr(op.xo.rt, res);
			//xer.ca = cout;
			//xer.ca = ~a[DWIDTH-1] ^ res[DWIDTH-1];
			xer.ca = carry_out(~a, 32'b0, res);
		end

		{1'bz, Xop_mulhwu}: begin
			Word u, v;

			no_oe = 1'b1;
			{u, v} = { {DWIDTH{1'b0}}, a} * { {DWIDTH{1'b0}}, b};
			res = u;
			rv.set_gpr(op.xo.rt, u);
		end

		{1'bz, Xop_mulhw}: begin
			longint prod64;   // longint is a signed 64bit integer
			longint a64, b64;

			a64 = { {DWIDTH{a[$left(a)]}}, a};
			b64 = { {DWIDTH{b[$left(b)]}}, b};

			no_oe = 1'b1;
			prod64 = a64 * b64;
			res = (prod64 & 64'hffffffff00000000) >> 32;
			rv.set_gpr(op.xo.rt, res);
			//$display("product: %d = %d * %d", prod64, a64, b64);
			//$display("product: %h = %h * %h", prod64, a64, b64);
		end

		{1'bz, Xop_mullw}: begin
			longint prod64;   // longint is a signed 64bit integer
			longint a64, b64;

			a64 = { {DWIDTH{a[$left(a)]}}, a};
			b64 = { {DWIDTH{b[$left(b)]}}, b};

			no_oe = 1'b1;

			prod64 = a64 * b64;
			res = (prod64 & 64'h00000000ffffffff);

			//Word u, v;
			//$display("mullw: %16h * %16h", 
				//{ {DWIDTH{a[$left(a)]}}, a}, { {DWIDTH{b[$left(b)]}}, b});

			//no_oe = 1'b1;
			//{u, v} = { {DWIDTH{a[$left(a)]}}, a} * { {DWIDTH{b[$left(b)]}}, b};
			//res = v;

			rv.set_gpr(op.xo.rt, res);

			if( op.xo.oe ) begin
				// overflow if result can not be represented in 32 bit
				if( prod64 != { {DWIDTH{res[DWIDTH-1]}}, res} )
					xer.ov = 1'b1;
				else
					xer.ov = 1'b0;

				xer.so = xer.ov | xer.so;
			end
		end

		{1'bz, Xop_divw}: begin
			no_oe = 1'b1;
			//if( (b == 0) || ((a == 32'h80_00_00_00) && (b == 32'hff_ff_ff_ff) ) )
				//res = 'z;
			// Prediction of special input combinations that would be illegal.
			// The prediction here reflects the behavior of the DW_div_seq module.
			if( b == 0 ) begin
				if( a[$left(a)] == 1'b0 )  // positive
					res = 32'hff_ff_ff_ff;
				else if( a[$left(a)] == 1'b1 )  // negative
					res = 32'h00_00_00_00;
			end else if( (a == 32'h80_00_00_00) && (b == 32'hff_ff_ff_ff) )
				res = 32'h80_00_00_00;
			else
				res = signed'(a) / signed'(b);

			rv.set_gpr(op.xo.rt, res);

			if( op.xo.oe ) begin
				// overflow if illegal operands used
				if( (a == 32'h80000000 && b == 32'hffffffff) || b == 0 )
					xer.ov = 1'b1;
				else
					xer.ov = 1'b0;

				xer.so = xer.ov | xer.so;
			end
		end

		{1'bz, Xop_divwu}: begin
			no_oe = 1'b1;
			//if( (b == 0) || ((a == 32'h80_00_00_00) && (b == 32'hff_ff_ff_ff) ) )
				//res = 'z;
			// Prediction of special input combinations that would be illegal.
			// The prediction here reflects the behavior of the DW_div_seq module.
			if( b == 0 ) 
				res = 32'hff_ff_ff_ff;
			else
				res = unsigned'(a) / unsigned'(b);

			rv.set_gpr(op.xo.rt, res);

			if( op.xo.oe ) begin
				// overflow if illegal operands used
				if( b == 32'b0 )
					xer.ov = 1'b1;
				else
					xer.ov = 1'b0;

				xer.so = xer.ov | xer.so;
			end
		end

		Xop_andc: begin
			no_oe = 1'b1;
			res = s & ~b;
			rv.set_gpr(op.x.ra, res);
		end
		
		Xop_and: begin
			no_oe = 1'b1;
			res = s & b;
			rv.set_gpr(op.x.ra, res);
		end

		Xop_or: begin
			no_oe = 1'b1;
			res = s | b;
			rv.set_gpr(op.x.ra, res);
		end

		Xop_orc: begin
			no_oe = 1'b1;
			res = s | ~b;
			rv.set_gpr(op.x.ra, res);
		end

		Xop_xor: begin
			no_oe = 1'b1;
			res = s ^ b;
			rv.set_gpr(op.x.ra, res);
		end

		Xop_nand: begin
			no_oe = 1'b1;
			res = ~(s & b);
			rv.set_gpr(op.x.ra, res);
		end

		Xop_nor: begin
			no_oe = 1'b1;
			res = ~(s | b);
			rv.set_gpr(op.x.ra, res);
		end

		Xop_eqv: begin
			no_oe = 1'b1;
			res = ~(s ^ b);
			rv.set_gpr(op.x.ra, res);
		end

		Xop_extsb: begin
			no_oe = 1'b1;
			res = { {24{s[7]}}, s[7:0] };
			rv.set_gpr(op.x.ra, res);
		end

		Xop_extsh: begin
			no_oe = 1'b1;
			res = { {24{s[15]}}, s[15:0] };
			rv.set_gpr(op.x.ra, res);
		end

		Xop_slw: begin
			no_oe = 1'b1;
			rot_n = b[4:0];
			res = rotl32(s, rot_n);
			//if( b[5] == 1'b0 ) 
				rot_mask = mask(31, rot_n);
			//else
			//	rot_mask = '0;

			res = res & rot_mask;
			rv.set_gpr(op.x.ra, res);
		end

		Xop_srw: begin
			no_oe = 1'b1;
			rot_n = b[4:0];
			res = rotl32(s, 32 - rot_n);

			//if( b[5] == 1'b0 )
				rot_mask = mask(31-rot_n, 0);
			//else
			//	rot_mask = '0;

			res = res & rot_mask;
			rv.set_gpr(op.x.ra, res);
		end

		Xop_srawi: begin
			no_oe = 1'b1;
			rot_n = op.x.rb;
			res = rotl32(s, 32-rot_n);
			rot_mask = mask(31-rot_n, 0);
			
			xer.ca = s[31] & (( res & ~rot_mask) != '0);
			res = (res & rot_mask) | ({32{s[31]}} & ~rot_mask);
			rv.set_gpr(op.x.ra, res);
		end

		Xop_sraw: begin
			no_oe = 1'b1;
			rot_n = b[4:0];
			res = rotl32(s, 32 - rot_n);

			//if( b[5] == 1'b0 )
				rot_mask = mask(31-rot_n, 0);
			//else
			//	rot_mask = '0;

			xer.ca = s[31] & ((res & ~rot_mask) != '0);
			res = (res & rot_mask) | ({32{s[31]}} & ~rot_mask);
			rv.set_gpr(op.x.ra, res);
		end

		Xop_cmp: begin
			no_oe = 1'b1;
			no_rc = 1'b1;
			
			if( a == b )
				cr.eq = 1'b1;
			else if( int'(a) > int'(b) )
				cr.gt = 1'b1;
			else if( int'(a) < int'(b) )
				cr.lt = 1'b1;

			cr.ov = xer.so;

			rv.set_cr(op.d.rt[4:2], cr);
		end

		Xop_cmpl: begin
			no_oe = 1'b1;
			no_rc = 1'b1;
			
			if( a == b )
				cr.eq = 1'b1;
			else if( unsigned'(a) > unsigned'(b) )
				cr.gt = 1'b1;
			else if( unsigned'(a) < unsigned'(b) )
				cr.lt = 1'b1;

			cr.ov = xer.so;

			rv.set_cr(op.d.rt[4:2], cr);
		end

		Xop_popcb: begin
			logic[7:0] n[0:3];

			no_oe = 1'b1;
			no_rc = 1'b1;

			for(int b=0; b<4; b++) begin
				n[b] = '0;
				for(int i=0; i<8; i++) begin
					if( s[b*8 + i] == 1'b1 ) n[b]++;
				end
			end

			rv.set_gpr(op.x.ra, {n[3], n[2], n[1], n[0]});
		end

/*		Xop_popcw: begin
			logic[15:0] n[0:1];

			no_oe = 1'b1;
			no_rc = 1'b1;

			for(int b=0; b<2; b++) begin
				for(int i=0; i<16; i++) begin
					if( s[b*16 + i] == 1'b1 ) n[b]++;
				end
			end

			rv.set_gpr(op.x.ra, {n[1], n[0]});
		end
*/

		Xop_prtyw: begin
			no_oe = 1'b1;
			no_rc = 1'b1;

			res = 32'h0;
			for(int i=0; i<4; i++)
				res[0] ^= s[i*8];
			
			rv.set_gpr(op.d.ra, res);
		end

		Xop_cntlzw: begin
			Word a;

			no_oe = 1'b1;
			
			a = state.get_gpr(op.x.rt);

			res = 32'd32;
			for(int i=DWIDTH-1; i>=0; i--)
				if( a[i] == 1'b1 ) begin
					res = 31-i;
					break;
				end

			rv.set_gpr(op.d.ra, res);
		end

		Xop_mtocrf: begin
			if( op.xfx.spr[9] == 1'b1 ) begin  // mtocrf form
				int crf;

				no_oe = 1'b1;
				no_rc = 1'b1;

				crf = 0;
				for(int i=0; i<8; i++)
					if( op.xfx.spr[8-i] == 1'b1 )
						crf = i;

				for(int i=0; i<4; i++) cr[3-i] = s[31-crf*4-i];
				rv.set_cr(crf, cr);
			end else begin                // mtcrf form
				Word gpr;

				no_oe = 1'b1;
				no_rc = 1'b1;

				gpr = state.get_gpr(op.xfx.rt);

				for(int i=0; i<8; i++)
					if( op.xfx.spr[8-i] == 1'b1 ) begin
						Cr_field crf;

						//for(int j=0; j<4; j++) 
							////crf[j] = gpr[((7-i)+1)*4-1 - j];
							//crf[j] = gpr[(8-i)*4-1 -j];

						crf.lt = gpr[(8-i)*4-1];
						crf.gt = gpr[(8-i)*4-1 -1];
						crf.eq = gpr[(8-i)*4-1 -2];
						crf.ov = gpr[(8-i)*4-1 -3];
						
						rv.set_cr(i, crf);
					end else
						rv.set_cr(i, state.get_cr(i));
			end
		end

		Xop_mfocrf: begin
			if( op.xfx.spr[9] == 1'b1 ) begin  // mfocrf form
				int crf;

				no_oe = 1'b1;
				no_rc = 1'b1;

				for(int i=0; i<8; i++)
					if( op.xfx.spr[8-i] == 1'b1 )
						crf = i;

				res = state.get_gpr(op.xfx.rt);
				//res = 32'hx;  // other fields are undefined
				cr = state.get_cr(crf);
				for(int i=0; i<4; i++) res[31-crf*4-i] = cr[3-i];

				rv.set_gpr(op.xfx.rt, res);
			end else begin                 // mfcr form
				Word gpr;

				for(int i=0; i<8; i++) begin
					Cr_field crf;

					crf = state.get_cr(i);
					
					gpr[(8-i)*4-1]    = crf.lt;
                    gpr[(8-i)*4-1 -1] = crf.gt;
                    gpr[(8-i)*4-1 -2] = crf.eq;
                    gpr[(8-i)*4-1 -3] = crf.ov;
				end

				rv.set_gpr(op.xfx.rt, gpr);
			end
		end

		Xop_wait: begin  // no change of state
			no_oe = 1'b1;
			no_rc = 1'b1;
		end

		Xop_ecowx, Xop_eciwx: begin
			Mem_model io;
			Address addr;

			no_oe = 1'b1;
			no_rc = 1'b1;

			io = state.get_io_model();
			addr = state.get_gpr(op.x.ra) + state.get_gpr(op.x.rb);

			if( op.x.xo == Xop_ecowx )
				io.set(addr[$left(addr):2], state.get_gpr(op.x.rt));
			else if( op.x.xo == Xop_eciwx )
				rv.set_gpr(op.x.rt, io.get(addr[$left(addr):2]));
		end
	endcase

	if( !no_oe && op.xo.oe ) begin
		if( op.xo.xo == Xop_neg )
			xer.ov = neg_ov;
		else
			xer.ov = res[$left(res)] ^ cout; 
		xer.so = xer.ov | xer.so;
	end

	rv.set_xer({xer, {29{1'b0}}});

	if( res === 'z ) begin
		cr.eq = 1'bz;
		cr.gt = 1'bz;
		cr.lt = 1'bz;
	end else if( res == 0 )
		cr.eq = 1'b1;
	else begin
		cr.gt = !res[DWIDTH-1];
		cr.lt = res[DWIDTH-1];
	end

	cr.ov = xer.so;

	if( !no_rc && op.xo.rc ) begin
		rv.set_cr(0, cr);
	end
endfunction
//---------------------------------------------------------------------------
function void
Predictor::predict_branch(ref Instruction inst, State state, Fixed_state rv);
	Address pc;
	Address nia;
	Inst op;
	logic ctr_ok, cond_ok;
	logic[0:DWIDTH-1] creg;
	logic[0:4] bo;
	logic[0:4] bi;
	
	op = inst.get();
	pc = state.get_pc();
	nia = state.get_pc() +1;
	
	creg = {
		state.get_cr(0),
		state.get_cr(1),
		state.get_cr(2),
		state.get_cr(3),
		state.get_cr(4),
		state.get_cr(5),
		state.get_cr(6),
		state.get_cr(7)
	};

	bo = op.b.bo;
	bi = op.b.bi;

	// decrement counter
	case(op.b.opcd)
		Op_bc: begin	
			if( bo[2] == 1'b0 )
				rv.set_ctr(state.get_ctr() - 1);
		end

		Op_bclr: begin
			if( op.xl.xo == Xxop_bclr || op.xl.xo == Xxop_bcctr ) begin
				dec_and_test_ctr_invalid: assert(!(op.xl.xo == Xxop_bcctr && op.xl.bt[2] == 1'b0));
				if( op.xl.xo == 16 && bo[2] == 1'b0 )
					rv.set_ctr(state.get_ctr() - 1);
			end
		end
	endcase
	
	ctr_ok = bo[2] | ((rv.get_ctr() != 0) ^ bo[3]);
	cond_ok = bo[0] | (creg[bi] == bo[1]);

	// save to link register
	case(op.i.opcd)
		Op_branch, Op_bc: begin
			if( op.i.lk == 1'b1 )
				rv.set_lnk((pc +1)<<2);
		end

		Op_bclr: begin
			if( op.xl.xo == Xxop_bclr || op.xl.xo == Xxop_bcctr ) begin
				if( op.i.lk == 1'b1 )
					rv.set_lnk((pc +1)<<2);
			end
		end
	endcase

	// calculate next instruction address
	case(op.i.opcd)
		Op_branch:
			if( op.i.aa )
				nia = { {8{op.i.li[$left(op.i.li)]}}, op.i.li};
			else
				nia = signed'(state.get_pc()) + signed'({{8{op.i.li[$left(op.i.li)]}}, op.i.li});

		Op_bc: begin
			if( ctr_ok && cond_ok )
				if( op.i.aa )
					nia = {{18{op.b.bd[$left(op.b.bd)]}}, op.b.bd};
				else
					nia = signed'(state.get_pc()) + signed'({{18{op.b.bd[$left(op.b.bd)]}}, op.b.bd});
		end

		Op_bclr: begin
			if( cond_ok && ctr_ok )
			case(op.xl.xo)
				Xxop_bclr:  nia = state.get_lnk() >> 2;
					Xxop_bcctr: nia = state.get_ctr() >> 2;
				endcase
		end
	endcase

	// condition register logical instructions
	if( op.xl.opcd == Op_bclr ) begin
		Cr_field crtmp;
		logic cbres, cba, cbb;
		bit is_log_inst = 1'b1;  // st to zero to don't affect the state if 
		                         // this is not a CR logical instruction
		
		crtmp = state.get_cr(op.xl.ba[4:2]);
		cba = crtmp[3 - op.xl.ba[1:0]];
		crtmp = state.get_cr(op.xl.bb[4:2]);
		cbb = crtmp[3 - op.xl.bb[1:0]];

		unique case(op.xl.xo)
			Xxop_crand:         cbres = cba & cbb;
			Xxop_cror:          cbres = cba | cbb;
			Xxop_crnand:        cbres = ~(cba & cbb);
			Xxop_crnor:         cbres = ~(cba | cbb);
			Xxop_crandc:        cbres = cba & ~cbb;
			Xxop_crorc:         cbres = cba | ~cbb;
			Xxop_crxor:         cbres = cba ^ cbb;
			Xxop_creqv:         cbres = ~(cba ^ cbb);
			default:            is_log_inst = 1'b0;
		endcase
		
		if( is_log_inst ) begin
			crtmp = state.get_cr(op.xl.bt[4:2]);
			crtmp[3 - op.xl.bt[1:0]] = cbres;
			rv.set_cr(op.xl.bt[4:2], crtmp);
		end else if( op.xl.xo == Xxop_mcrf ) begin
			crtmp = state.get_cr(op.xl.ba[4:2]);
			rv.set_cr(op.xl.bt[4:2], crtmp);
		end
	end

	rv.set_pc(nia);
endfunction
//---------------------------------------------------------------------------
function void
Predictor::predict_load_store(ref Instruction inst, State state, Fixed_state rv);
	Inst op;
	Address ea;
	Address b;
	Word w;
	Word rt;
	logic[15:0] cop;
	bit misaligned;

	op = inst.get();
	ea = 0;
	misaligned = 1'b0;

	if( op.d.ra == 0 )
		b = 0;
	else
		b = state.get_gpr(op.d.ra);

	cop = {op.d.opcd, op.x.xo};
	casez(cop)
		{Op_stw, 10'bz}, {Op_sth, 10'bz}, {Op_stb, 10'bz}, 
		{Op_lwz, 10'bz}, {Op_lhz, 10'bz}, {Op_lbz, 10'bz},
		{Op_stwu, 10'bz}, {Op_sthu, 10'bz}, {Op_stbu, 10'bz},
		{Op_lwzu, 10'bz}, {Op_lhzu, 10'bz}, {Op_lbzu, 10'bz},
		{Op_lha, 10'bz}, {Op_lhau, 10'bz},
		{Op_lmw, 10'bz}, {Op_stmw, 10'bz}:
		begin
			ea = b + { {16{op.d.d[15]}}, op.d.d };
		end

		{Op_alu_xo, Xop_stwx}, {Op_alu_xo, Xop_sthx},{Op_alu_xo, Xop_stbx},
		{Op_alu_xo, Xop_lwzx},{Op_alu_xo, Xop_lhzx},{Op_alu_xo, Xop_lbzx},
		{Op_alu_xo, Xop_lhax}, {Op_alu_xo, Xop_lhaux},
		{Op_alu_xo, Xop_stwux}, {Op_alu_xo, Xop_sthux}, {Op_alu_xo, Xop_stbux},
		{Op_alu_xo, Xop_lwzux}, {Op_alu_xo, Xop_lhzux}, {Op_alu_xo, Xop_lbzux}:
		begin
			ea = b + state.get_gpr(op.x.rb);
		end
	endcase

	w = state.get_mem(ea >> 2);
	rt = state.get_gpr(op.d.rt);


	casez(cop)
		{Op_stw, 10'bz}, {Op_alu_xo, Xop_stwx},
		{Op_stwu, 10'bz}, {Op_alu_xo, Xop_stwux}:
		begin
			if( ea[1:0] == 2'b0 )  // only affect memory if access correctly 
			                       // aligned
				// There is only a limited amount of memory available
				// the effective address ea is modulo'ed to the implemented
				// range
				rv.set_mem(ea >> 2, rt);
			else
				misaligned = 1'b1;
		end

		{Op_sth, 10'bz}, {Op_alu_xo, Xop_sthx},
		{Op_sthu, 10'bz}, {Op_alu_xo, Xop_sthux}:
		begin
			case(ea[1:0])
				2'b10: w[15:0] = rt[15:0];
				2'b01: w[23:8] = rt[15:0];
				2'b00: w[31:16] = rt[15:0];
				default: misaligned = 1'b1;
			endcase
				
			rv.set_mem(ea >> 2, w);
		end

		{Op_stb, 10'bz}, {Op_alu_xo, Xop_stbx},
		{Op_stbu, 10'bz}, {Op_alu_xo, Xop_stbux}:
		begin
			case(ea[1:0])
				2'b11: w[7:0] = rt[7:0];
				2'b10: w[15:8] = rt[7:0];
				2'b01: w[23:16] = rt[7:0];
				2'b00: w[31:24] = rt[7:0];
				default: misaligned = 1'b1;
			endcase

			rv.set_mem(ea >> 2, w);
		end

		{Op_lwz, 10'bz}, {Op_alu_xo, Xop_lwzx},
		{Op_lwzu, 10'bz}, {Op_alu_xo, Xop_lwzux}:
		begin
			if( ea[1:0] == 2'b0 )
				rv.set_gpr(op.d.rt, w);
			else begin // unaligned access
				//rv.set_gpr(op.d.rt, 32'h0);
				misaligned = 1'b1;
			end
		end

		{Op_lhz, 10'bz}, {Op_alu_xo, Xop_lhzx},
		{Op_lhzu, 10'bz}, {Op_alu_xo, Xop_lhzux}:
		begin
			case(ea[1:0])
				2'b10: w = { 16'h0, w[15:0] };
				2'b01: w = { 16'h0, w[23:8] };
				2'b00: w = { 16'h0, w[31:16] };
				default: begin
					w = 32'h0;
					misaligned = 1'b1;
				end
			endcase

			if( !misaligned )
				rv.set_gpr(op.d.rt, w);
		end

		{Op_lha, 10'bz}, {Op_alu_xo, Xop_lhax},
		{Op_lhau, 10'bz}, {Op_alu_xo, Xop_lhaux}:
		begin
			case(ea[1:0])
				2'b10: w = { {16{w[15]}}, w[15:0] };
				2'b01: w = { {16{w[23]}}, w[23:8] };
				2'b00: w = { {16{w[31]}}, w[31:16] };
				default: begin
					w = 32'h0;
					misaligned = 1'b1;
				end
			endcase

			if( !misaligned )
				rv.set_gpr(op.d.rt, w);
		end

		{Op_lbz, 10'bz}, {Op_alu_xo, Xop_lbzx},
		{Op_lbzu, 10'bz}, {Op_alu_xo, Xop_lbzux}:
		begin
			case(ea[1:0])
				2'b00: w = { 24'h0, w[31:24] };
				2'b01: w = { 24'h0, w[23:16] };
				2'b10: w = { 24'h0, w[15: 8] };
				2'b11: w = { 24'h0, w[ 7: 0] };
				default: misaligned = 1'b1;
			endcase

			if( !misaligned )
				rv.set_gpr(op.d.rt, w);
		end

		{Op_lmw, 10'bz}:
		begin
			if( ea[1:0] == 2'b0 ) begin
				for(int i=op.d.rt; i<32; i++) begin
					rv.set_gpr(i, state.get_mem(ea >> 2));
					ea = ea + 4;
				end
			end else begin // unaligned access
				//rv.set_gpr(op.d.rt, 32'h0);
				misaligned = 1'b1;
			end
		end

		{Op_stmw, 10'bz}:
		begin
			if( ea[1:0] == 2'b0 )  // only affect memory if access correctly 
			                       // aligned
				for(int i=op.d.rt; i<32; i++) begin
					//$display("stmw %2d  mem[%08h] = %08h", i, ea >> 2, rv.get_gpr(i));
					rv.set_mem(ea >> 2, rv.get_gpr(i));
					ea = ea + 4;
				end
			else
				misaligned = 1'b1;
		end
	endcase

	// update forms
	if( !misaligned ) begin
		casez(cop)
			{Op_stwu, 10'bz}, {Op_sthu, 10'bz}, {Op_stbu, 10'bz},
			{Op_lwzu, 10'bz}, {Op_lhzu, 10'bz}, {Op_lbzu, 10'bz},
			{Op_lhau, 10'bz}, {Op_alu_xo, Xop_lhaux},
			{Op_alu_xo, Xop_stwux}, {Op_alu_xo, Xop_sthux}, {Op_alu_xo, Xop_stbux},
			{Op_alu_xo, Xop_lwzux}, {Op_alu_xo, Xop_lhzux}, {Op_alu_xo, Xop_lbzux}:
			begin
				rv.set_gpr(op.d.ra, ea);
			end
		endcase
	end 

	if( misaligned ) begin
		// take interrupt
		Msr msr_int_mask;
		Esr esr;

		$display("alignment interrupt");

		msr_int_mask = '0;
		msr_int_mask.ce = 1'b1;
		msr_int_mask.me = 1'b1;
		msr_int_mask.de = 1'b1;

		esr = '0;

		rv.set_srr0(state.get_pc()<<2);
		rv.set_srr1(state.get_msr() & msr_mask);

		rv.set_msr(state.get_msr() & msr_int_mask);
		rv.set_esr(esr);
	end
endfunction
//---------------------------------------------------------------------------
function void 
Predictor::predict_rotate(ref Instruction inst, State state, Fixed_state rv);
	Inst op;
	logic[4:0] n;
	Word res;
	Word m;
	Word s;
	Word a;
	Word b;
	Xer xer;
	Word xer_word;
	Cr_field cr;


	op = inst.get();
	a = state.get_gpr(op.m.ra);
	b = state.get_gpr(op.m.rb);
	s = state.get_gpr(op.m.rs);
	xer_word = state.get_xer();
	xer = xer_word[31:29];
	cr = '0;

	case(op.m.opcd)
		Op_rlwimi: begin
			n = op.m.rb;
			res = rotl32(s, n);
			m = mask(DWIDTH-1-op.m.mb, DWIDTH-1-op.m.me);
			res = (res & m) | (a & ~m);
			rv.set_gpr(op.m.ra, res);
		end

		Op_rlwinm: begin
			n = op.m.rb;
			res = rotl32(s, n);
			m = mask(DWIDTH-1-op.m.mb, DWIDTH-1-op.m.me);
			res = (res & m);
			rv.set_gpr(op.m.ra, res);
		end

		Op_rlwnm: begin
			n = b[4:0];
			res = rotl32(s, n);
			m = mask(DWIDTH-1-op.m.mb, DWIDTH-1-op.m.me);
			res = res & m;
			rv.set_gpr(op.m.ra, res);
		end
	endcase

	if( res == 0 )
		cr.eq = 1'b1;
	else begin
		cr.gt = !res[DWIDTH-1];
		cr.lt = res[DWIDTH-1];
	end

	cr.ov = xer.so;

	if( op.m.rc ) begin
		rv.set_cr(0, cr);
	end
endfunction
//---------------------------------------------------------------------------
function void 
Predictor::predict_gpr_spr_moves(ref Instruction inst, State state, Fixed_state rv);
	Inst op;
	Word spr;
	Word gpr;
	
	op = inst.get();
	gpr = state.get_gpr(op.xfx.rt);
	
	case(op.xfx.spr)
		Spr_xer:    spr = state.get_xer();
		Spr_ctr:    spr = state.get_ctr();
		Spr_lnk:    spr = state.get_lnk();
		Spr_srr0:   spr = state.get_srr0();
		Spr_srr1:   spr = state.get_srr1();
		Spr_csrr0:  spr = state.get_csrr0();
		Spr_csrr1:  spr = state.get_csrr1();
		Spr_mcsrr0: spr = state.get_mcsrr0();
		Spr_mcsrr1: spr = state.get_mcsrr1();
		Spr_esr:    spr = state.get_esr();
		Spr_dear:   spr = state.get_dear();
		Spr_gin:    spr = '0;  // gin always reads zero in SIT
		Spr_gout:   spr = state.get_gout();
		Spr_goe:    spr = state.get_goe();
		default:    spr = '0;
	endcase

	if( op.xfx.xo == Xop_mfspr )
		rv.set_gpr(op.xfx.rt, spr);
	else if( op.xfx.xo == Xop_mtspr ) begin
		case(op.xfx.spr)
			Spr_xer:    rv.set_xer(gpr & {3'b111, 29'b0});
			Spr_ctr:    rv.set_ctr(gpr);
			Spr_lnk:    rv.set_lnk(gpr);
			Spr_srr0:   rv.set_srr0(gpr);
			Spr_srr1:   rv.set_srr1(gpr);
			Spr_csrr0:  rv.set_csrr0(gpr);
			Spr_csrr1:  rv.set_csrr1(gpr);
			Spr_mcsrr0: rv.set_mcsrr0(gpr);
			Spr_mcsrr1: rv.set_mcsrr1(gpr);
			Spr_esr:    rv.set_esr(gpr & esr_mask);
			Spr_dear:   rv.set_dear(gpr);
			Spr_gout:   rv.set_gout(gpr);
			Spr_goe:    rv.set_goe(gpr);
		endcase
	end
endfunction
//---------------------------------------------------------------------------
function void
Predictor::predict_interrupt_return(ref Instruction inst, State state, 
		Fixed_state rv);
	Inst op;

	op = inst.get();

	if( op.xl.xo == Xxop_rfi ) 
	begin
		rv.set_msr(state.get_srr1() & msr_mask);
		rv.set_pc(state.get_srr0() >> 2);
	end 
	else if( op.xl.xo == Xxop_rfci ) 
	begin
		rv.set_msr(state.get_csrr1() & msr_mask);
		rv.set_pc(state.get_csrr0() >> 2);
	end
	else if( op.xl.xo == Xxop_rfmci ) 
	begin
		rv.set_msr(state.get_mcsrr1() & msr_mask);
		rv.set_pc(state.get_mcsrr0() >> 2);
	end
endfunction
//---------------------------------------------------------------------------
function void
Predictor::predict_gpr_msr_moves(ref Instruction inst, State state, 
		Fixed_state rv);
	Inst op;

	op = inst.get();

	if( op.x.xo == Xop_mtmsr ) begin
		rv.set_msr(state.get_gpr(op.x.rt) & msr_mask);
	end else if( op.x.xo == Xop_mfmsr ) begin
		rv.set_gpr(op.x.rt, state.get_msr() & msr_mask);
	end
endfunction
//---------------------------------------------------------------------------
function void
Predictor::predict_trap(ref Instruction inst, State state,
		Fixed_state rv);
	Inst op;
	Word a, b;
	logic[0:4] to;
	bit take_int;

	op = inst.get();
	a = state.get_gpr(op.d.ra);
	to = op.d.rt;
	take_int = 1'b0;

	if( op.d.opcd == Op_twi )
		b = { {32{op.d.d[15]}}, op.d.d };
	else if( op.x.opcd == Op_alu_xo && op.x.xo == Xop_tw )
		b = state.get_gpr(op.x.rb);

	if( to[0] & (signed'(a) < signed'(b)) )
		take_int = 1'b1;
	
	if( to[1] & (signed'(a) > signed'(b)) )
		take_int = 1'b1;

	if( to[2] & (a == b) )
		take_int = 1'b1;

	if( to[3] & (a < b) )
		take_int = 1'b1;

	if( to[4] & (a > b) )
		take_int = 1'b1;

	if( take_int ) begin
		Msr msr_int_mask;
		Esr esr;

		msr_int_mask = '0;
		msr_int_mask.ce = 1'b1;
		msr_int_mask.me = 1'b1;
		msr_int_mask.de = 1'b1;

		esr = '0;
		esr.ptr = 1'b1;

		rv.set_srr0(0);
		rv.set_srr1(state.get_msr() & msr_mask);

		rv.set_msr(state.get_msr() & msr_int_mask);
		rv.set_esr(esr);
	end
endfunction
//---------------------------------------------------------------------------
function void 
Predictor::predict_never(ref Instruction inst,
		State state,
		Fixed_state rv);

	Inst op;

	op = inst.get();

	if( op.x.opcd == Op_nvecmpi ) begin
		Word tmp;
		Nve_sstate res;

		tmp = state.get_gpr(op.d.ra);

		for(int i=0; i<8; i++) begin
			if( tmp[(i+1)*4-1 -: 4] == op.d.d[3:0] )
				res[i] = 1'b1;
			else
				res[i] = 1'b0;
		end

		rv.set_nve_sstate(res);
	end else if( op.x.opcd == Op_nve_xo ) begin
		if( op.x.xo == Xop_nvem ) begin
			Word res;
			Nve_lut lut;

			res = state.get_gpr(op.x.ra);
			lut = state.get_nve_lut(op.x.rb);

			for(int i=0; i<8; i++) begin
				res[(i+1)*4-1 -: 4] = lut[res[(i+1)*4-1 -: 4]];
			end

			rv.set_gpr(op.x.rt, res);
		end else if( op.x.xo == Xop_nves ) begin
			Word res;
			Word a, b;
			Nve_sstate sel;

			a = state.get_gpr(op.x.ra);
			b = state.get_gpr(op.x.rb);
			sel = state.get_nve_sstate();
		
			for(int i=0; i<8; i++) begin
				res[(i+1)*4-1 -: 4] = sel[i] ? b[(i+1)*4-1 -: 4] : a[(i+1)*4-1 -: 4];
			end	

			rv.set_gpr(op.x.rt, res);
		end else if( op.x.xo == Xop_nvemtl ) begin
			Nve_lut lut;
			Word a,b;

			a = state.get_gpr(op.x.ra);
			b = state.get_gpr(op.x.rb);

			lut[0:7] = a;
			lut[8:15] = b;
			//for(int i=0; i<8; i++) 
				//lut[i] = a[(i+1)*4-1 -: 4];

			//for(int i=8; i<16; i++)
				//lut[i] = b[(i+1)*4-1 -: 4];

			$display("nvemtl: a = %08h, b = %08h, LUT = %08h",
				a, b, lut);

			rv.set_nve_lut(op.x.rt, lut);
		end
	end

endfunction
//---------------------------------------------------------------------------
function logic[31:0]
Predictor::rotl32(input logic[31:0] x, int d);
	logic[63:0] y = '0;

	y[31:0] = x;
	y = y << d;

	for(int i=0; i<d; i++) y[i] = y[32 +i];

	return y[31:0];
endfunction
//---------------------------------------------------------------------------
function logic[31:0]
Predictor::mask(input int mstart, int mend);
	logic[31:0] rv = '0;

	if( mstart >= mend )
		for(int i=mend; i<=mstart; i++) rv[i] = 1'b1;
	else begin
		//for(int i=0; i<=mend; i++) rv[i] = 1'b1;
		//for(int i=mstart; i<32; i++) rv[i] = 1'b1;
		for(int i=0; i<=mstart; i++) rv[i] = 1'b1;
		for(int i=mend; i<32; i++) rv[i] = 1'b1;
	end

	return rv;
endfunction
//---------------------------------------------------------------------------
function logic
Predictor::carry_out(input Word a, Word b, Word y);
	logic an = a[$left(a)];
	logic bn = b[$left(b)];
	logic yn = y[$left(y)];

	return an & bn | (yn ^ an ^ bn) & (an | bn);
endfunction
//---------------------------------------------------------------------------

`endif
