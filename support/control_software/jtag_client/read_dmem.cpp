#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include <stdexcept>
#include <algorithm>
#include <bitset>
#include <sstream>
#include <fstream>
#include <boost/format.hpp>
#include <boost/program_options.hpp>

extern "C" {
#include <urjtag/urjtag.h>
#include <urjtag/chain.h>
#include <urjtag/part.h>
#include <urjtag/part_instruction.h>
#include <urjtag/data_register.h>
#include <urjtag/tap_register.h>
#include <urjtag/cmd.h>
}

typedef std::vector<unsigned int> Mem_vec;

static const char bsdl_path[] = "/afsuser/sfriedma/bsdl";


class Chain
{
	urj_chain_t* chain;
	bool echo_on;

	public:
	Chain()
	{
		chain = urj_tap_chain_alloc();
		echo_on = false;
	}

	~Chain()
	{
		urj_tap_chain_free(chain);
	}


	void echo(bool o) { echo_on = o; }
	bool echo() const { return echo_on; }

	void run_cmd(const std::string& cmd)
	{
		using namespace std;

		if( chain == 0 )
			throw runtime_error("chain == 0 in run_cmd()");

		char** param;
		int num_space = count(cmd.begin(), cmd.end(), ' ');
		size_t i = 0;
		size_t j = 0;
		int i_word = 0;

		if( echo_on )
			cout << "CMD: " << cmd << '\n';

		try {
			param = new char* [num_space+2];
			param[num_space+1] = 0;

			//cout << "looking for " << num_space+1 << " words" << endl;
			while( j != string::npos ) {
				size_t sz;

				j = cmd.find(' ', i);
				if( j == string::npos )
					sz = cmd.length() - i;
				else
					sz = j - i;

				param[i_word] = new char [sz+2];
				cmd.copy(param[i_word], sz, i);
				param[i_word][sz] = 0;
				//cout << i_word << " : '" << param[i_word] << "'" << endl;

				i = j+1;
				i_word++;

			}

			if( urj_cmd_run(chain, param) != URJ_STATUS_OK )
				throw runtime_error((boost::format("executing UrJTAG command '%s' failed") % cmd).str());
		} catch(...) {
			for(int k=0; k<i_word+1; k++) {
				delete [] param[k];
			}

			delete [] param;

			throw;
		}

		for(int k=0; k<num_space+1; k++) {
			delete [] param[k];
		}

		delete [] param;
	}

	template<int width>
	std::bitset<width> read_bitset()
	{
		urj_part_t *part;
		urj_tap_register_t *r;
		urj_data_register_t *dr;
		urj_part_instruction_t *active_ir;

		//if (urj_cmd_test_cable (chain) != URJ_STATUS_OK)
			//throw std::runtime_error("read_uint(): test cable failed");

		part = urj_tap_chain_active_part (chain);
		if (part == NULL)
			throw std::runtime_error("read_uint(): No active part");

		active_ir = part->active_instruction;
		if (active_ir == NULL)
		{
			throw std::runtime_error("read_uint(): No active instruction");
		}
		dr = active_ir->data_register;
		if (dr == NULL)
		{
			throw std::runtime_error("read_uint(): Active instruction without data register");
		}
	
		std::string bitstr(urj_tap_register_get_string(dr->out));

		return std::bitset<width>(bitstr.substr(bitstr.length()-width));
	}

	unsigned int read_uint()
	{
		//urj_part_t *part;
		//urj_tap_register_t *r;
		//urj_data_register_t *dr;
		//urj_part_instruction_t *active_ir;

		////if (urj_cmd_test_cable (chain) != URJ_STATUS_OK)
			////throw std::runtime_error("read_uint(): test cable failed");

		//part = urj_tap_chain_active_part (chain);
		//if (part == NULL)
			//throw std::runtime_error("read_uint(): No active part");

		//active_ir = part->active_instruction;
		//if (active_ir == NULL)
		//{
			//throw std::runtime_error("read_uint(): No active instruction");
		//}
		//dr = active_ir->data_register;
		//if (dr == NULL)
		//{
			//throw std::runtime_error("read_uint(): Active instruction without data register");
		//}

		//return urj_tap_register_get_value(dr->out);

		return read_bitset<sizeof(unsigned int)*8>().to_ulong();

		/*if (dir)
			r = dr->out;
		else
			r = dr->in;
		urj_log (URJ_LOG_LEVEL_NORMAL, "%s (0x%0*" PRIX64 ")\n",
				 urj_tap_register_get_string (r), r->len / 4,
				 urj_tap_register_get_value (r));*/
	}

};

void hello()
{
	Chain chain;

	chain.run_cmd("cable xpc_ext");
	chain.run_cmd(std::string("bsdl path ") + bsdl_path);
	chain.run_cmd("detect");
	chain.run_cmd("part 0");

}

void read_mem(Mem_vec::iterator it, int addr_start, int addr_stop, const std::string& init_file)
{
	using namespace std;

	Chain chain;
	static const std::bitset<32> data_dummy(0xaffe);

	//chain.echo(true);
	chain.run_cmd(std::string("include ") + init_file);
	//chain.run_cmd("cable xpc_ext");
	//chain.run_cmd(std::string("bsdl path ") + bsdl_path);
	//chain.run_cmd("detect");
	//chain.run_cmd("part 0");
	//chain.run_cmd("register BR 1");
	//chain.run_cmd("register CR 1");
	//chain.run_cmd("register DMR 45");
	//chain.run_cmd("register IMR 45");
	//chain.run_cmd("register ID 32");
	//chain.run_cmd("instruction CTRL 1111100010 CR");
	//chain.run_cmd("instruction DM 1111000010 DMR");
	//chain.run_cmd("instruction IM 1111000011 IMR");

	chain.run_cmd("instruction DM");
	chain.run_cmd("shift ir");

	for(int i=addr_start; i < addr_stop; i++) {
		std::bitset<13> addr_bits(i);
		chain.run_cmd((boost::format("dr 0%s%s")   // '0' is the we bit -> do not write
					% addr_bits.to_string() 
					% data_dummy.to_string()).str());
		chain.run_cmd("shift dr");
		chain.run_cmd("shift dr");
		//chain.run_cmd("dr out");
		//chain.run_cmd("dr out");
		//cout << "0x" << hex << setw(8) << setfill('0') << chain.read_uint() << '\n';
		//cout << chain.read_bitset<46>().to_string() << '\n';
		*(it++) = chain.read_uint();
	}
	cout << dec;
}

void hexdump(const Mem_vec::iterator& a, const Mem_vec::iterator& b, std::ostream& out)
{
	using namespace std;

	static const int words_per_line = 8;
	int ctr = 0;

	for(Mem_vec::iterator i=a; i != b; i++) {
		out << hex << setw(8) << setfill('0') << *i << "  ";

		if( (++ctr % words_per_line) == 0 )
			out << '\n';
			
	}
}

int main(int argc, char* argv[])
{
	using namespace std;
	namespace po = boost::program_options;

	std::string out_file;
	size_t mem_off = 0;
	size_t mem_size = 10;

	Mem_vec mem;

	po::options_description desc("Options");
	desc.add_options()
		("help,h", "Produce help message")
		("offset,o", po::value<size_t>(&mem_off)->default_value(0), 
		 "Offset address for reading")
		("size,s", po::value<size_t>(&mem_size)->default_value(32),
		 "Amount of words to read starting at offset")
		("file,f", po::value<string>(&out_file)->default_value("-"),
		 "Output file for memory dump. '-' for stdout.");

	po::variables_map vm;
	po::store(po::parse_command_line(argc, argv, desc), vm);
	po::notify(vm);

	if( vm.count("help") ) {
		cout << desc << endl;
		return 0;
	}

	mem.resize(mem_size);
	read_mem(mem.begin(), mem_off, mem_off+mem_size, "./init_file.cfg");

	if( out_file != "-" ) {
		ofstream of;
		of.open(out_file.c_str());
		cout << "\nDumping memory contents to " << out_file << "\n";
		hexdump(mem.begin(), mem.end(), of);
	} else {
		cout << "\n=== Data memory contents in hexadecimal ===\n";
		hexdump(mem.begin(), mem.end(), cout);
		cout << dec 
			<< "\n=== End of hexdump ==="
			<< endl;
	}

	return 0;
}
