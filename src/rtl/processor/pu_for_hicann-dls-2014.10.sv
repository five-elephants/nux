// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Pu_for_hicann_dls_2014_10
	(	input logic             clk,
		input logic             reset,

		input logic             hold,  // actually: hold instruction fetch 
		
		//Gpr_file.processor  gpr_file,
		Ram_if.client           imem,
		Ram_if.client           dmem,
		Bus_if.master           dmem_bus,
		Bus_if.master           iobus,
		Bus_if.master           vector_bus,
		Bus_if.master           vector_pbus,
		
		output Pu_types::Word   gout,
		input  Pu_types::Word   gin,
		output Pu_types::Word   goe,
		
		Pu_ctrl_if.pu           ctrl,
		Timer_if.pu             timer,

		Syn_io_if.client        syn_io_a,
		Syn_io_if.client        syn_io_b
	);

	Pu_v2
	#(	
		/** Configure the branch predictor:
		* 0  : Disable branch prediction
		* >0 : Use branch prediction. The parameter then specifies how many
		* instruction address bits are used for the prediction table. */
		.OPT_BCACHE(4),

		/** Set this option to integrate a multiply functional unit. */
		.OPT_MULTIPLIER(1'b1),

		/** Set this option to integrate a divide functional unit. */
		.OPT_DIVIDER(1'b1),

		/** Set this option to use the iobus module. */
		.OPT_IOBUS(1'b0),

		/** Set this option to include the fixed-point vector SIMD unit */
		.OPT_VECTOR(1'b1),

		/** The vector functional unit uses multiple datapath slices in
		* parallel. Since it is an SIMD unit, all slices execute the same
		* instruction, but on different data using local registers. */
		.OPT_VECTOR_SLICES(1),

		/** One vector consists of multiple 16 bit wide half-word elements. This
		* option configures how many of them are implemented. */
		.OPT_VECTOR_NUM_HALFWORDS(8),

		/** Configure the delay of the vector multiplier. */
		.OPT_VECTOR_MULT_DELAY(4),

		/** Configure the delay of the vector adder after the multiplier. */
		.OPT_VECTOR_ADD_DELAY(1),

		/** Number of entries in the instruction queue from
		* general-purpose processor to vector unit. */
		.OPT_VECTOR_INST_QUEUE_DEPTH(4),

		/** Set this option to use the NibblE VEctoR Extension (NEVER) */
		.OPT_NEVER(1'b0),

		/** Set this option to use the SYNapse ProceSsing Extension (SYNAPSE) */
		.OPT_SYNAPSE(1'b0),

		/** Select the data memory interface:
		* MEM_TIGHT  -  Using the Ram_if port dmem for memories with
		*               a guaranteed fixed latency.
		* MEM_BUS    -  Using the OCP Bus_if port dmem_bus for ports with
		*               arbitrary latency. */
		.OPT_DMEM(Pu_types::MEM_BUS),

		/** Set the number of pipeline registers between the instruction
		* memory and the predecode stage. */
		.OPT_IF_LATENCY(1),

		/** Removes a long timing path: bcache does not predict for
		* instruction locations that are targets of branches. */
		.OPT_BCACHE_IGNORES_JUMPS(1'b1),

		/** A write to the GPR file is passed to the reader in the same cycle
		* */
		.OPT_WRITE_THROUGH(1'b1),

		/** Instruction tracking for GPRs uses the lookup-cache method.
		* Required if delayed write-back to GPRs is used (e.g. OPT_DMEM
		* = MEM_BUS). */
		.OPT_LOOKUP_CACHE(1'b1)
	) pu (
		.*
	);

endmodule
