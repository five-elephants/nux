// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



package Program_pkg;
	import Pu_types::Word;

	//---------------------------------------------------------------------------
	/** Load a raw binary image from file filename and write its contents to
	* mem. */
	function automatic void read_raw_image(input string filename, ref Word mem[]);
		int binf;
		int i;

		i = 0;
		binf = $fopen(filename, "rb");
		assert(binf != 0) else begin
			$error("Could not open file '%s' for reading", filename);
			return;
		end

		while( !$feof(binf) ) begin
			mem[i][31:24] = $fgetc(binf);
			mem[i][23:16] = $fgetc(binf);
			mem[i][15: 8] = $fgetc(binf);
			mem[i][ 7: 0] = $fgetc(binf);

			++i;
		end
		$fclose(binf);

		$display("read_raw_image: read %d words from '%s'",
			i, filename);
	endfunction
	//---------------------------------------------------------------------------

	//---------------------------------------------------------------------------
	/** Read a mem (ASCII hexdump) file that contains data words of 8 bit and
	* store the contents to mem as 32 bit words. */
	function automatic void read_text_byte_image(input string filename, 
			ref Word mem[], 
			input int num_bytes);
		logic[7:0] tmp[];
		
		tmp = new [num_bytes];

		$readmemh(filename, tmp);

		for(int i=0; i<num_bytes/4; i++) begin
			mem[i][31:24] = tmp[4*i];
			mem[i][23:16] = tmp[4*i+1];
			mem[i][15: 8] = tmp[4*i+2];
			mem[i][ 7: 0] = tmp[4*i+3];
		end
	endfunction
	//---------------------------------------------------------------------------

	//---------------------------------------------------------------------------
	/** Dump the contents of array mem as raw binary image. */
	function automatic void write_raw_image(input string filename, 
			const ref Word mem[]);
		int binf;

		binf = $fopen(filename, "w");
		for(int i=0; i<mem.size(); i++) begin
			//$fwrite(binf, "%u", {mem[i][31:24], mem[i][23:16], mem[i][15:8], mem[i][7:0]});
			$fwrite(binf, "%u", {mem[i][7:0], mem[i][15:8], mem[i][23:16], mem[i][31:24]});
		end
		$fclose(binf);
	endfunction
	//---------------------------------------------------------------------------
endpackage
