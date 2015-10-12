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

module Program_test 
	#(	IMEM_ADDR_WIDTH = 12,
		DMEM_ADDR_WIDTH = 12,
   		OPT_VECTOR_SLICES = 8 ); 

localparam int VECTOR_PBUS_WIDTH = 128 * OPT_VECTOR_SLICES;

const time clk_period = 10ns;
logic clk;
logic reset;
logic pu_hold;

int issue_ctr;
int cycle_ctr;
bit disable_count;


Pu_ctrl_if pu_ctrl();
Timer_if timer_if();
Ram_if #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_if();
Ram_if #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_if();

Bus_if #(.byteen(1'b1)) dmem_bus_if(.Clk(clk)),
		vector_bus_if(.Clk(clk)),
		memory_bus_if(.Clk(clk));
Bus_if iobus_if(.Clk(clk));
Bus_if #(
	.byteen(1'b1),
	.data_width(VECTOR_PBUS_WIDTH)
) vector_pbus_if(.Clk(clk));

Syn_io_if syn_io_a_if(), syn_io_b_if();

//L1_memory #(.ADDR_WIDTH(IMEM_ADDR_WIDTH), .IS_DUALPORT(1'b0)) imem 
	//(	.clk(clk),
		//.reset(reset),
		////.intf(imem_if_ram),
		//.intf(imem_if),
		//.intf2(imem_dummy_if) );

//L1_memory #(.ADDR_WIDTH(DMEM_ADDR_WIDTH), .IS_DUALPORT(1'b0)) dmem
	//(	.clk(clk),
		//.reset(reset),
		////.intf(dmem_if_2),
		//.intf(dmem_if),
		//.intf2(dmem_dummy_if) );

Sim_memory #(
	.ADDR_WIDTH(IMEM_ADDR_WIDTH),
	.RAND_DELAY_RATE(0.0)
) imem (
	.clk, .reset,
	.intf(imem_if)
);

Sim_memory #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem (
	.clk, .reset,
	.intf(dmem_if)
);



Iobus_dummy #(
	.RD_ACCEPT_LATENCY(0),
	.WR_ACCEPT_LATENCY(0),
	.RD_RETURN_LATENCY(0),
	.WR_RETURN_LATENCY(0),
	.RESPONSE_FUNCTION(1)  // work as memory
) iobus_dummy (
	.clk, .reset,
	.iobus(iobus_if)
);

Iobus_dummy #(
	.RD_ACCEPT_LATENCY(0),
	.WR_ACCEPT_LATENCY(0),
	.RD_RETURN_LATENCY(0),
	.WR_RETURN_LATENCY(0),
	.RESPONSE_FUNCTION(1),  // work as memory
	.BYTE_ENABLED(1'b1),
	.DATA_WIDTH(VECTOR_PBUS_WIDTH)
) mem_bus (
	.clk, .reset,
	.iobus(vector_pbus_if)
);

Syn_io_dummy syn_io_a_dummy (
	.clk, .reset,
	.syn_io(syn_io_a_if)
);

Syn_io_dummy syn_io_b_dummy (
	.clk, .reset,
	.syn_io(syn_io_b_if)
);
//Iobus_dummy #(
	//.RD_ACCEPT_LATENCY(0),
	//.WR_ACCEPT_LATENCY(0),
	//.RD_RETURN_LATENCY(0),
	//.WR_RETURN_LATENCY(0),
	//.RESPONSE_FUNCTION(1),  // work as memory
	//.BYTE_ENABLED(1'b1)
//) mem_bus (
	//.clk, .reset,
	//.iobus(dmem_bus_if)
//);


//Ram_delay #( 
	//.NUM_STAGES(2),
	//.ADDR_WIDTH(DMEM_ADDR_WIDTH),
	//.DATA_WIDTH(32)
//) delay_imem (
	//.clk(clk),
	//.reset(reset),
	//.mem(imem_if_ram),
	//.client(imem_if)
//);

//Ram_delay #( 
	//.NUM_STAGES(3),
	//.ADDR_WIDTH(DMEM_ADDR_WIDTH),
	//.DATA_WIDTH(32)
//) delay_dmem (
	//.clk(clk),
	//.reset(reset),
	//.mem(dmem_if_2),
	//.client(dmem_if)
//);

Bus_if_arb #(
	.RESET_BY_0(1)
) memory_arb (
	.in_0(dmem_bus_if),
	.in_1(vector_bus_if),
	.out(memory_bus_if)
);

Bridge_bus2ram bus2ram(memory_bus_if, dmem_if);

Pu_v2 #(
	.OPT_BCACHE(4),
	.OPT_MULTIPLIER(1'b1),
	.OPT_DIVIDER(1'b1),
	.OPT_IOBUS(1'b1),
	.OPT_VECTOR(1'b1),
	.OPT_VECTOR_SLICES(OPT_VECTOR_SLICES),
	.OPT_NEVER(1'b1),
	.OPT_SYNAPSE(1'b1),
	.OPT_DMEM(MEM_BUS),
	//.OPT_DMEM(MEM_TIGHT),
	.OPT_IF_LATENCY(1) )
	uut
	(	.clk(clk),
		.reset(reset),
		.hold(pu_hold),
		.imem(imem_if),
		.dmem(dmem_if),
		.dmem_bus(dmem_bus_if),
		.iobus(iobus_if),
		.vector_bus(vector_bus_if),
		.vector_pbus(vector_pbus_if),
		.gout(),
		.goe(),
		.gin(),
		.ctrl(pu_ctrl),
		.timer(timer_if),
		.syn_io_a(syn_io_a_if),
		.syn_io_b(syn_io_b_if)
	);

Interrupt_ctrl interrupt_ctrl (
	.clk(clk),
	.reset(reset),
	.pu_ctrl(pu_ctrl.ctrl),
	//.ctrl(intf),
	.doorbell(1'b0),
	.timer(timer_if.int_ctrl),
	.en_clk(),
	.gin(32'b0)
);

Timer_unit timer (
	.clk, .reset,
	.intf(timer_if)
);


always #(clk_period/2) clk = ~clk;

assign pu_hold = 1'b0;

/** Count issued instructions and total clock cycles to calculate CPI */
always @(posedge clk)
begin
	if( pu_ctrl.sleep )
		disable_count <= 1'b1;
	else
		disable_count <= 1'b0;

	if( !reset && !disable_count ) begin
		for(int i=0; i<Frontend::FUB_ID_END; i++) begin
			if( uut.issue[i].valid )
				//&& !(i == Frontend::FUB_ID_BRANCH && uut.frontend.fst_d.predicted_taken) )
			begin
				issue_ctr <= issue_ctr +1;
				break;
			end
		end
		cycle_ctr <= cycle_ctr +1;
	end
end

//---------------------------------------------------------------------------
// Loads programs from memory description files and checks the result
//---------------------------------------------------------------------------
class Program;
	const string base_path = "../../test/testcode/";

	string name;
	string code_img;  // code memory image
	string data_img;  // data memory image
	string eres_img;  // expected result
	//logic[DWIDTH-1 : 0] cmp_mem[0 : (2**DMEM_ADDR_WIDTH)-1];
	logic[7:0] cmp_mem[0 : (2**DMEM_ADDR_WIDTH)*4 -1];
	time exe_time;
	bit ends_with_wait;

	int num_issues;
	int num_cycles;
	real cpi;

	int cnt_branches;
	int cnt_mis_taken;
	int cnt_mis_not_taken;

	function new(input string n, time et, string d = "");
		name = n;
		code_img = { base_path, name, "_code.mem" };
		eres_img = { base_path, name, "_exp.mem" };

		if( d == "" )
			data_img = { base_path, name, ".mem" };
		else
			data_img = d;

		exe_time = et;
		cpi = 0;

		ends_with_wait = 1'b1;
	endfunction

	/** Load instruction and data image from file
	 *
	 * Data memory is treated special to account for data being stored byte-
	 * wise. So the temporary image is an array of bytes, which is filled by
	 * $readmemh(). Using an array of words here leads to alignment problems,
	 * when not all bytes in a word are set.
	 * */
	virtual function void load();
		//Word imemimg[0 : 2**IMEM_ADDR_WIDTH -1];
		//Word dmemimg[0 : 2**DMEM_ADDR_WIDTH -1];
		//logic[7:0] dmemimg[0 : (2**DMEM_ADDR_WIDTH)*4 -1];
		Word imemimg[];
		Word dmemimg[];

		imemimg = new [2**IMEM_ADDR_WIDTH];
		dmemimg = new [2**DMEM_ADDR_WIDTH];

		// reset memories to all undefined
		for(int i=0; i<(2**IMEM_ADDR_WIDTH); i++) begin
			imem.mem[i] = 'x;
		end

		for(int i=0; i<(2**DMEM_ADDR_WIDTH); i++) begin
			dmem.mem[i] = 'x;
		end

		$readmemh(code_img, imemimg);
		Program_pkg::read_text_byte_image(data_img, dmemimg, (2**DMEM_ADDR_WIDTH)*4);
		$readmemh(eres_img, cmp_mem);

		// copy images to memories
		for(int i=0; i<(2**IMEM_ADDR_WIDTH); i++) begin
			imem.mem[i] = imemimg[i];
		end

		for(int i=0; i<(2**DMEM_ADDR_WIDTH); i++) begin
			dmem.mem[i] = dmemimg[i];
		end

		issue_ctr = 0;
		cycle_ctr = 0;
		disable_count = 1'b0;
	endfunction
	
	virtual function bit check();		
		logic[7:0] dmemimg[0 : (2**DMEM_ADDR_WIDTH)*4 -1];
		bit success;


		// calculate CPI
		num_issues = issue_ctr;
		num_cycles = cycle_ctr;
		cpi = real'(cycle_ctr) / real'(issue_ctr);

		for(int i=0; i<(2**DMEM_ADDR_WIDTH); i++) begin
			dmemimg[4*i+3] = dmem.mem[i][ 7: 0];
			dmemimg[4*i+2] = dmem.mem[i][15: 8];
			dmemimg[4*i+1] = dmem.mem[i][23:16];
			dmemimg[4*i]   = dmem.mem[i][31:24];
		end

		success = 1'b1;
		for(int i=0; i<(2**DMEM_ADDR_WIDTH)*4; i++) begin
			if( !(dmemimg[i] === cmp_mem[i]) )
				success = 1'b0;

			check_compare_data_image: assert (dmemimg[i] === cmp_mem[i]) else
			  $error("Data image does not fit to reference image '%s' at address %08h (expected=%02h, got=%02h)",
				  eres_img, i, cmp_mem[i], dmemimg[i]);
		end

		//if( cmp_mem === dmemimg )
		if( success )
			return 1'b1;
		else begin
			string dump_file;
			string bin_dump_file;
			Word dump_img[];

			dump_img = new [2**DMEM_ADDR_WIDTH];

			dump_file = {"dump_", name};
			for(int i=0; i<dump_file.len(); i++)
				if( dump_file[i] == "/" )
					dump_file[i] = "_";

			bin_dump_file = {dump_file, ".bin"};
			dump_file = {dump_file, ".mem"};

			for(int i=0; i<2**DMEM_ADDR_WIDTH; i++) begin
				dump_img[i] = {dmem.mem[i][31:24], dmem.mem[i][23:16], dmem.mem[i][15:8], dmem.mem[i][7:0]};
			end
			Program_pkg::write_raw_image(bin_dump_file, dump_img);

			$display("dumping to %s", dump_file);
			$writememh(dump_file, dmemimg);
			return 1'b0;
		end
	endfunction
endclass
//---------------------------------------------------------------------------
class Raw_program extends Program;

	function new(input string n, time et, string d = "");
		super.new(n, et, d);
		code_img = { base_path, name, "_code.raw" };
		eres_img = { base_path, name, "_exp.mem" };

		if( d == "" )
			data_img = { base_path, name, "_data.raw" };
		else
			data_img = d;
	endfunction

	virtual function void load();
		Word imemimg[];
		Word dmemimg[];

		imemimg = new [2**IMEM_ADDR_WIDTH];
		dmemimg = new [2**DMEM_ADDR_WIDTH];

		// reset memories to all undefined
		for(int i=0; i<(2**IMEM_ADDR_WIDTH); i++) begin
			imem.mem[i] = 'x;
		end

		for(int i=0; i<(2**DMEM_ADDR_WIDTH); i++) begin
			dmem.mem[i] = 'x;
		end

		Program_pkg::read_raw_image(code_img, imemimg);
		Program_pkg::read_raw_image(data_img, dmemimg); // XXX

		$readmemh(eres_img, cmp_mem);

		// copy images to memories
		for(int i=0; i<(2**IMEM_ADDR_WIDTH); i++) begin
			imem.mem[i] = imemimg[i];
		end

		for(int i=0; i<(2**DMEM_ADDR_WIDTH); i++) begin
			dmem.mem[i] = dmemimg[i];
		end

		issue_ctr = 0;
		cycle_ctr = 0;
		disable_count = 1'b0;
	endfunction
endclass
//--------------------------------------------------------------------------------
class Raw_program_with_raw_exp extends Raw_program;
	function new(input string n, time et, string d = "");
		super.new(n, et, d);
		code_img = { base_path, name, "_code.raw" };
		eres_img = { base_path, name, "_exp.raw" };

		if( d == "" )
			data_img = { base_path, name, "_data.raw" };
		else
			data_img = d;
	endfunction

	virtual function void load();
		Word imemimg[];
		Word dmemimg[];
		Word cmpimg[];

		imemimg = new [2**IMEM_ADDR_WIDTH];
		dmemimg = new [2**DMEM_ADDR_WIDTH];
		cmpimg = new [2**DMEM_ADDR_WIDTH];

		// reset memories to all undefined
		for(int i=0; i<(2**IMEM_ADDR_WIDTH); i++) begin
			imem.mem[i] = 'x;
		end

		for(int i=0; i<(2**DMEM_ADDR_WIDTH); i++) begin
			dmem.mem[i] = 'x;
		end

		Program_pkg::read_raw_image(code_img, imemimg);
		Program_pkg::read_raw_image(data_img, dmemimg);
		Program_pkg::read_raw_image(eres_img, cmpimg);

		// copy images to memories
		for(int i=0; i<(2**IMEM_ADDR_WIDTH); i++) begin
			imem.mem[i] = imemimg[i];
		end

		for(int i=0; i<(2**DMEM_ADDR_WIDTH); i++) begin
			dmem.mem[i] = dmemimg[i];

			cmp_mem[4*i+3] = cmpimg[i][ 7: 0];
			cmp_mem[4*i+2] = cmpimg[i][15: 8];
			cmp_mem[4*i+1] = cmpimg[i][23:16];
			cmp_mem[4*i]   = cmpimg[i][31:24];
		end

		issue_ctr = 0;
		cycle_ctr = 0;
		disable_count = 1'b0;
	endfunction

endclass
//---------------------------------------------------------------------------
//parameter int num_progs = 28;
parameter int num_progs = 22;
//parameter int num_progs = 1;
Program progs[0:num_progs-1];
bit success[0:num_progs-1];
bit all_success = 1'b1;
string cur_prog = "none";
real avg_cpi = 0.0;
int cur_time = 0;

initial begin : main
	Raw_program cshell;
	Raw_program time_base;
	Raw_program bcache_bench;
	Raw_program coremark;
	Raw_program_with_raw_exp fxv_test;
	Raw_program_with_raw_exp vector_stdp_kernel;
	Raw_program_with_raw_exp sync;

	progs[0] = new("load_add_store", 500ns);
	progs[1] = new("branch", 500ns, "../../test/testcode/empty.mem");
	progs[2] = new("branch_cond", 1200ns, "../../test/testcode/empty.mem");
	progs[3] = new("simple_interlock_test", 2us);
	progs[4] = new("interlocks", 1700ns);
	progs[5] = new("logic", 4us, "../../test/testcode/empty.mem");
	progs[6] = new("func_call", 20us, "../../test/testcode/empty.mem");
	progs[7] = new("special_reg", 2us, "../../test/testcode/empty.mem");
	cshell = new("c/cshell", 20us, "../../test/testcode/c/cshell_data.raw");
	progs[8] = cshell; 
	progs[9] = new("load_with_update", 20us);
	progs[10] = new("mem_multiple", 20us);
	progs[11] = new("mul", 20us, "../../test/testcode/empty.mem");
	progs[12] = new("interrupt", 4us, "../../test/testcode/empty.mem");
	progs[13] = new("div", 20us, "../../test/testcode/empty.mem");
	progs[14] = new("cr_complex", 4us);
	progs[15] = new("other_instructions", 4us, "../../test/testcode/empty.mem");
	progs[16] = new("debugging", 4us, "../../test/testcode/empty.mem");
	progs[17] = new("io", 10us, "../../test/testcode/empty.mem");
	progs[18] = new("ext_ctrl", 10us, "../../test/testcode/empty.mem");
	fxv_test = new ("fxv_test", 100us);
	progs[19] = fxv_test;
	vector_stdp_kernel = new ("vector_stdp_kernel", 3ms);
	progs[20] = vector_stdp_kernel;
	sync = new ("sync", 1us);
	progs[21] = sync;


	//progs[19] = new("timer", 60us, "../../test/testcode/empty.mem");
	//progs[19].ends_with_wait = 1'b0;
	//time_base = new("c/time_base", 50us, "../../test/testcode/c/time_base_data.raw");
	//progs[20] = time_base;
	//progs[21] = new("never", 50us, "../../test/testcode/empty.mem");
	//progs[22] = new("tn_testflow/prime", 10us, "../../test/testcode/tn_testflow/prime_data.mem");
	//progs[23] = new("tn_testflow/fibonacci", 10us, "../../test/testcode/tn_testflow/fibonacci_data.mem");
	//progs[24] = new("tn_testflow/kmp_search", 10us, "../../test/testcode/tn_testflow/kmp_search_data.mem");
	//progs[25] = new("tn_testflow/maze", 10us, "../../test/testcode/tn_testflow/maze_data.mem");
	//progs[26] = new("tn_testflow/operators", 10us, "../../test/testcode/tn_testflow/operators_data.mem");
	//progs[27] = new("tn_testflow/switch", 10us, "../../test/testcode/tn_testflow/switch_data.mem");

	//progs[0] = new("load_add_store", 500ns);
	//progs[0] = new("interrupt", 4us, "../../test/testcode/empty.mem");

	//progs[0] = new("never", 50us, "../../test/testcode/empty.mem");
	//progs[1] = new("synapse", 50us, "../../test/testcode/empty.mem");

	//bcache_bench = new("c/bcache_bench", 3ms, "../../test/testcode/c/bcache_bench_data.raw");
	//progs[27] = bcache_bench;
	//progs[27] = new("c/bcache_bench", 3ms, "../../test/testcode/empty.mem");

	//progs[28] = new("tn_testflow/tn_testflow", 10us, "../../test/testcode/tn_testflow/tn_testflow_data.mem");

	//progs[21] = new("c/io_test", 50us, "../../test/testcode/c/io_test_data.mem");
	//progs[21] = new("c/matrix", 1ms, "../../test/testcode/matrix_data.mem");

	//progs[9] = new("blinker", 100us, "../../test/testcode/empty.mem");
	//progs[10] = new("c/eblinker", 100us, "../../test/testcode/c/eblinker_data.mem");
	
	//progs[0] = new("coremark_v1.0/coremark", 1500ms, "../../test/testcode/coremark_v1.0/coremark_data.mem");
	//progs[0] = new("coremark", 100ms);

	//coremark = new("coremark", 10ms);
	//progs[0] = coremark;

	//progs[0] = new("ext_ctrl", 10us, "../../test/testcode/empty.mem");
	
	clk = 1'b0;
	reset = 1'b1;

	//pu_ctrl.wakeup = 1'b0;
	//pu_ctrl.doorbell = 1'b0;
	//pu_ctrl.ext_input = 1'b0;

	@(negedge clk);

	for(int i=0; i<num_progs; i++) begin : loop
		$display("loading program '%s'", progs[i].name);
		cur_prog = progs[i].name;

		reset = 1'b1;
		progs[i].load();
		#(10*clk_period) reset = 1'b0;

		if( progs[i].ends_with_wait )
			@(pu_ctrl.sleep == 1'b1);
		else
			#(progs[i].exe_time);

		// get performance metrices
		progs[i].cnt_branches = uut.fub_branch.cnt_branches;
		progs[i].cnt_mis_taken = uut.fub_branch.cnt_mis_taken;
		progs[i].cnt_mis_not_taken = uut.fub_branch.cnt_mis_not_taken;

		check_with_expected: assert(progs[i].check()) begin
			$display("test program %d passed.", i);
			success[i] = 1'b1;
		end else begin
			$display("test program %d FAILED.", i);
			success[i] = 1'b0;
			all_success = 1'b0;
		end
	end : loop

	$display("=====================================================");
	$display("SUMMARY:");
	for(int i=0; i<num_progs; i++) begin
		avg_cpi = avg_cpi + progs[i].cpi;

		if( success[i] )
			if( progs[i].cnt_branches != 0 ) begin
				$display("   prog %2d %30s : ok          CPI = %2.2f (%4d/%4d) | BP:(T:%2.2f + NT:%2.2f / %4d)",
					i, progs[i].name, progs[i].cpi, progs[i].num_cycles, progs[i].num_issues,
					real'(progs[i].cnt_mis_taken) / real'(progs[i].cnt_branches),
					real'(progs[i].cnt_mis_not_taken) / real'(progs[i].cnt_branches),
					progs[i].cnt_branches);
			end else begin
				$display("   prog %2d %30s : ok          CPI = %2.2f (%4d/%4d) | BP:(--no branches--)",
					i, progs[i].name, progs[i].cpi, progs[i].num_cycles, progs[i].num_issues);
			end
		else
			$display("   prog %2d %30s : failed      CPI = %2.2f (%4d/%4d)",
				i, progs[i].name, progs[i].cpi, progs[i].num_cycles, progs[i].num_issues);
	end

	avg_cpi = avg_cpi / real'(num_progs);
	$display(" average CPI = %.2f", avg_cpi);

	if( all_success == 1'b1 )
		$display("All programs successfull");
	else
		$display("Some programs failed");

	$stop();

end : main

always begin
	#(1ms);
	cur_time = cur_time + 1;
	$display("=== 1ms tick: time = %d ms ===", cur_time);
end

//---------------------------------------------------------------------------
/*covergroup cg_hold_stats @(posedge clk);
	hold: coverpoint uut.decode_ctrl.hold iff(~reset);
	hold_branch: coverpoint uut.decode_ctrl.hold_branch iff(~reset);
	hold_data: coverpoint uut.decode_ctrl.hold_data iff(~reset);
endgroup

cg_hold_stats cg_hold_stats_inst = new ();*/
//---------------------------------------------------------------------------

endmodule

/* vim: set noet fenc= ff=unix sts=0 sw=4 ts=4 : */
