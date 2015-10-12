// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


import Frontend::*;

module Inst_stream_test();

localparam time clk_period = 10ns;
localparam int addr_width = 12;
localparam int bcache_width = 8;
localparam int output_delay = 0;
localparam bit use_bcache = 1'b1;

typedef logic[addr_width-1:0] Addr;

logic clk, reset;
logic hold;
logic jump;
Addr jump_vec;
logic fb_taken;
logic fb_not_taken;
Addr fb_pc;
logic trans_cmplt;
Addr pc, npc;
Pu_inst::Inst inst;
logic predicted_taken;
logic valid;

Branch_control bctrl;
Fetch_state fst;

assign 
	bctrl.jump = jump,
	bctrl.jump_vec = jump_vec,
	bctrl.fb_taken = fb_taken,
	bctrl.fb_not_taken = fb_not_taken,
	bctrl.fb_pc = fb_pc;

assign
	trans_cmplt = fst.trans_cmplt,
	pc = fst.pc,
	npc = fst.npc,
	inst = fst.inst,
	predicted_taken = fst.predicted_taken,
	valid = fst.valid;
	

Ram_if #(
	.ADDR_WIDTH(addr_width),
	.DATA_WIDTH(32)
) imem ();


Inst_stream #(
	.addr_width(addr_width),
	.use_bcache(use_bcache),
	.bcache_width(bcache_width),
	.output_delay(output_delay)
) uut (
	.*
);

Sim_memory #(
	.ADDR_WIDTH(addr_width),
	.DATA_WIDTH(32)
) inst_mem (
	.clk, .reset,
	.intf(imem)
);

always begin
	clk = 1'b0;
	#(clk_period/2);
	clk = 1'b1;
	#(clk_period/2);
end
//---------------------------------------------------------------------------
class Rand_branch_program;
	int num_branches;
	Addr tab[];
	real prob[];
	Addr targets[];
	int predict_hit[];
	int predict_miss[];
	int not_a_branch;

	function new(input int num_branches);
		this.num_branches = num_branches;

		tab = new [num_branches];
		prob = new [num_branches];
		targets = new [num_branches];
		predict_hit = new [num_branches];
		predict_miss = new [num_branches];
		not_a_branch = 0;

		foreach(tab[i]) begin
			tab[i] = $urandom;
			if( $urandom_range(1000) > 500 )
				prob[i] = 0.9;
				//prob[i] = 1.0;
			else
				prob[i] = 0.1;
				//prob[i] = 0.0;
			targets[i] = $urandom;
			predict_miss[i] = 0;
			predict_hit[i] = 0;
		end
	endfunction

	function automatic bit branch(input Addr pc, logic pre_taken, output Addr target, logic fb_t, fb_nt);
		int found;

		found = -1;
		fb_t = 1'b0;
		fb_nt = 1'b0;

		foreach(tab[i])
			if( tab[i] == pc ) begin
				found = i;
				break;
			end

		if( found == -1 ) begin
			if( pre_taken ) begin
				//$display("not_a_branch at %d", $time);
				not_a_branch++;
				target = pc+1;
				fb_nt = 1'b1;
				return 1'b1;
			end
		end else begin
			if( real'($urandom_range(10000))/10000.0 <= prob[found] ) begin
				target = targets[found];

				// branch is taken and indicate jump if not predicted correctly
				if( pre_taken && (npc == target) )
					predict_hit[found]++;
				else
					predict_miss[found]++;

				fb_t = 1'b1;
				fb_nt = 1'b0;
				return !pre_taken || (npc != target);
			end else begin
				// branch is not taken
				if( pre_taken )
					predict_miss[found]++;
				else
					predict_hit[found]++;

				fb_t = 1'b0;
				fb_nt = 1'b1;
				target = pc+1;

				return pre_taken;
			end
		end

		return 1'b0;
	endfunction

	function automatic void stat();
		int tot_hit;
		int tot_miss;
		real avg_visit;

		tot_hit = 0;
		tot_miss = 0;
		avg_visit = 0.0;

		foreach(predict_hit[i]) begin
			tot_hit = tot_hit + predict_hit[i];
			avg_visit = (avg_visit + real'(predict_hit[i]+predict_miss[i]))/2.0;
		end

		foreach(predict_miss[i]) begin
			tot_miss = tot_miss + predict_miss[i];
		end

		$display("Branch prediction statistics:");
		$display("  hits:          %5d  (%3f)",
			tot_hit, real'(tot_hit)/real'(tot_hit+tot_miss+not_a_branch));
		$display("  misses:        %5d  (%3f)", 
			tot_miss+not_a_branch, 
			real'(tot_miss+not_a_branch)/real'(tot_hit+tot_miss+not_a_branch));
		$display("  not a branch:  %5d  (%3f)",
			not_a_branch, real'(not_a_branch)/real'(tot_hit+tot_miss+not_a_branch));
		$display("  total:  %5d", tot_hit + tot_miss + not_a_branch);

		$display("\naverage visits per branch: %3f", avg_visit);
	endfunction
endclass
//---------------------------------------------------------------------------
class Traced_program;
	typedef struct {
		int pc;
		logic[31:0] inst;
	} Trace_point;

	typedef struct {
		Addr addr;
		Addr target;
		bit seq[];
		int seq_ptr;
	} Branch_entry;

	const int seq_sz = 20;

	Trace_point trace[];
	Branch_entry branch_table[];
	int num_branches;
	int trace_sz;
	int trace_ptr;

	//---------------------------------------------------------------------------
	function new(input int unsigned num_branches, trace_sz);
		this.num_branches = num_branches;
		this.trace_sz = trace_sz;
		branch_table = new [num_branches];
		trace = new [trace_sz];
		trace_ptr = 0;
	endfunction
	//---------------------------------------------------------------------------
	function automatic void gen_branch_table(input int unsigned step);
		int unsigned addr;
		int unsigned i;
		int seq_rthresh;

		//addr = $urandom_range(step);
		addr = 0;
		i = 0;

		while( (addr < (2**addr_width-1)) && (i<num_branches) ) begin
			branch_table[i].addr = addr;
			branch_table[i].target = $urandom_range(2**addr_width-1);
			branch_table[i].seq = new [seq_sz];
			branch_table[i].seq_ptr = 0;

			if( $urandom_range(10000) > 5000 )
				seq_rthresh = 0.9;
			else
				seq_rthresh = 0.1;

			for(int j=0; j<seq_sz; j++) begin
				branch_table[i].seq[j] = ($urandom_range(10000) > seq_rthresh) ? 1'b1 : 1'b0;
			end

			addr = addr + $urandom_range(step, 1);
			i = i +1;
		end
	endfunction
	//---------------------------------------------------------------------------
	function automatic void gen_trace(ref logic[31:0] mem[0:(2**addr_width)-1]);
		int addr;
		int found;

		addr = 0;

		for(int i=0; i<trace_sz; i++) begin
			found = -1;

			// record trace point
			trace[i].pc = addr;
			trace[i].inst = mem[addr];

			// is there a branch at this address
			foreach(branch_table[j])
				if( branch_table[j].addr == addr ) begin
					found = j;
					break;
				end

			addr = (addr + 1) % (2**addr_width);
			if( found != -1 ) begin  // this is a branch
				if( branch_table[found].seq[branch_table[found].seq_ptr] ) begin
					addr = branch_table[found].target;
				end

				branch_table[found].seq_ptr = (branch_table[found].seq_ptr + 1) % seq_sz;
			end
		end

		// reset sequence pointers to start
		foreach(branch_table[i])
			branch_table[i].seq_ptr = 0;
	endfunction
	//---------------------------------------------------------------------------
	function automatic bit check_trace(input int pc, logic[31:0] inst);
		bit rv;

		rv = 1'b0;

		if( (pc == trace[trace_ptr].pc) && (inst == trace[trace_ptr].inst) )
			rv = 1'b1;
		else
			$display("check_trace mismatch on %d: got: PC=%08h, INST=%08h | expected: PC=%08h, INST=%08h",
				trace_ptr, pc, inst, trace[trace_ptr].pc, trace[trace_ptr].inst);

		trace_ptr++;

		return rv;
	endfunction
	//---------------------------------------------------------------------------
	function automatic bit branch(input Addr pc, logic pre_taken, output Addr target, logic fb_t, fb_nt);
		int found;

		found = -1;
		fb_t = 1'b0;
		fb_nt = 1'b0;

		foreach(branch_table[i])
			if( branch_table[i].addr == pc ) begin
				found = i;
				break;
			end

		if( found == -1 ) begin
			if( pre_taken ) begin
				//$display("not_a_branch at %d", $time);
				//not_a_branch++;
				target = pc+1;
				fb_nt = 1'b1;
				return 1'b1;
			end
		end else begin
			if( branch_table[found].seq[branch_table[found].seq_ptr] ) begin
				// branch is taken and indicate jump if not predicted correctly
				//if( pre_taken )
					//predict_hit[found]++;
				//else
					//predict_miss[found]++;

				fb_t = 1'b1;
				fb_nt = 1'b0;
				target = branch_table[found].target;
				return !pre_taken || (npc != target);
			end else begin
				// branch is not taken
				//if( pre_taken )
					//predict_miss[found]++;
				//else
					//predict_hit[found]++;

				fb_t = 1'b0;
				fb_nt = 1'b1;
				target = pc+1;

				return pre_taken;
			end

			branch_table[found].seq_ptr = (branch_table[found].seq_ptr + 1) % seq_sz;
		end

		return 1'b0;
	endfunction
	//---------------------------------------------------------------------------
endclass
//---------------------------------------------------------------------------
Rand_branch_program rbp;
Traced_program tp;

function automatic void init_mem_rand();
	for(int i=0; i<2**addr_width; i++)
		inst_mem.mem[i] = $urandom;
endfunction

task automatic do_jump(input Addr dest);
	jump_vec = dest;
	jump = 1'b1;

	#(clk_period);
	jump = 1'b0;
endtask

task automatic test_branch_program(ref Rand_branch_program rbp, input int num_cycles);
	Addr target;
	int bcnt;

	bcnt = 0;

	//while(bcnt < num_branches) begin
	for(int cycle=0; cycle<num_cycles; cycle++) begin
		fb_pc = pc;
		if( rbp.branch(pc, predicted_taken, target, fb_taken, fb_not_taken) ) begin
			do_jump(target);
			bcnt++;
		end else begin
			jump_vec = target;
			#(clk_period);
		end
	end

	rbp.stat();
endtask

task automatic test_trace(ref Traced_program tp);
	Addr target;
	bit in_trans;
	const int hold_thresh = 100;
	const int hold_test_max = 1000;

	tp.gen_branch_table(30);
	tp.gen_trace(inst_mem.mem);

	in_trans = 1'b0;
	for(int i=0; i<tp.trace_sz; i++) begin
		while( !valid ) #(clk_period);
		if( in_trans )
			while( !trans_cmplt ) #(clk_period);

		in_trans = 1'b0;

		check_trace: assert(tp.check_trace(pc, inst))
			else $error("Deviation from trace at PC=%8h inst=%8h",
				pc, inst); 

		if( $urandom_range(hold_test_max) < hold_thresh ) begin
			hold = 1'b1;

			for(int j=0; j<$urandom_range(10); j++)
				#(clk_period);

			hold = 1'b0;
		end

		fb_pc = pc;
		if( tp.branch(pc, predicted_taken, target, fb_taken, fb_not_taken) ) begin
			do_jump(target);
			//bcnt++;
			in_trans = 1'b1;
		end else begin
			jump_vec = target;
			#(clk_period);
		end
	end
endtask
//---------------------------------------------------------------------------
initial begin
	rbp = new(0.3*(2**addr_width-1));
	tp = new(0.3*(2**addr_width-1), 10000);

	reset = 1'b1;

	hold = 1'b0;
	jump = 1'b0;
	jump_vec = '0;
	fb_taken = 1'b0;
	fb_not_taken = 1'b0;
	fb_pc = '0;

	init_mem_rand();

	#(10*clk_period);
	@(negedge clk);

	reset = 1'b0;

	//#(100*clk_period);

	//do_jump($urandom);
	//do_jump($urandom);

	//#(100*clk_period);


	//repeat(10) begin
		//do_jump($urandom);
		//#($urandom_range(100)*clk_period);
	//end

	test_branch_program(rbp, 1000000);

	reset = 1'b1;
	#(10*clk_period);
	reset = 1'b0;

	test_trace(tp);

	$stop;

end
//---------------------------------------------------------------------------

property matched_to_memory;
	Pu_inst::Inst i;
	Addr a;

	@(posedge clk) disable iff(reset)
	( (valid, i = inst, a = pc) |-> (i === inst_mem.mem[a]) );
endproperty

check_matched_to_memory: assert property(matched_to_memory);


property control_transfer;
	Addr a;

	@(posedge clk) disable iff(reset)
	( (jump, a = jump_vec) |-> ##(2+output_delay) (pc == a) && trans_cmplt );
endproperty

check_control_transfer: assert property(control_transfer);
//---------------------------------------------------------------------------

endmodule
