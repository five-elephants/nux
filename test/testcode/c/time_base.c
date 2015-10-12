// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#define GET_TBU(x) asm("mfspr %0, 285" : "=r"(x) ::)
#define GET_TBL(x) asm("mfspr %0, 284" : "=r"(x) ::)

typedef unsigned int uint32_t;
typedef unsigned long long int uint64_t;
typedef uint64_t time_base_t;

uint32_t get_tbu()
{
	uint32_t tbu;

	asm("mfspr %0, 285"
			: "=r"(tbu)  /* output */
			: /* no input */
			: /* no clobber */);

	return tbu;
}


uint32_t get_tbl()
{
	uint32_t tbl;

	asm("mfspr %0, 284"
			: "=r"(tbl)  /* output */
			: /* no input */
			: /* no clobber */);

	return tbl;
}


time_base_t get_time_base()
{
	uint64_t tbu, tbl;
	time_base_t rv;

	GET_TBU(tbu);
	GET_TBL(tbl);

	rv = (tbu << 32) | tbl;   // how does this look in assembler?

	return rv;
}


//-----------------------------------------------------------------------------

volatile time_base_t delta;

void start()
{
	time_base_t a, b;
	int i;

	a = get_time_base();

	for(i=0; i<500; i++) {
		asm volatile("nop");
	}

	b = get_time_base();

	delta = b - a;
}


