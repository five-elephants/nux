// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#define SIMULATION

#define NUM_PATTERNS 3
#ifdef SIMULATION
	#define WAIT_CYCLES 10
#else
	/*#define WAIT_CYCLES 10000000*/
	#define WAIT_CYCLES 100000000
#endif  /* SIMULATION */

char patterns[NUM_PATTERNS] = { 0xf0, 0x96, 0xc3 };

static void wait_sec()
{
	int i;
	for(i=0; i<WAIT_CYCLES; i++)
		asm volatile("nop");
}

static void led(char nibble)
{
  static const unsigned int oe = 0xf;

	asm(
    "mtspr 0b0001000011, %0\n"
    "mtspr 0b0001000010, %1\n" 
			: /* no output */
			: "r"(oe), "r"(nibble)
			: /* no clobber */
  );
}

void start()
{
	int i = 0;
	int j;
	char c;

	//while( 1 ) {
	for(j=0; j<3*NUM_PATTERNS; j++) {
		c = patterns[i] >> 4;
		led(c);

		c = patterns[i];
		wait_sec();
		led(c);

		i = (i == NUM_PATTERNS-1) ? 0 : (i+1);
		//if( ++i >= NUM_PATTERNS )
		//	i = 0;

		wait_sec();
	}
}

