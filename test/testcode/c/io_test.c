// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#define IO_BASE  (0xc0000000)
#define RAM_BASE (0x00000000)
#define RAM_SIZE (128)

volatile unsigned int* io_ram = IO_BASE + RAM_BASE;

void io_read_block(volatile unsigned int* src, unsigned int* dest, unsigned int size)
{
	unsigned int i;
	for(i=0; i<size; i++)
		dest[i] = src[i];
}

void acc_block()
{
	unsigned int tmp[RAM_SIZE];
	int i;
	unsigned int acc = 0;

	io_read_block(io_ram, tmp, RAM_SIZE);

	for(i=0; i<RAM_SIZE; i++) {
		acc += tmp[i];
	}

	io_ram[0] = acc;
}


/** This is a random number generator called multiply with carry (MWC) as
 * proposed by George Marsaglia. */
unsigned int random()
{
	static unsigned int z = 521288629;
	static unsigned int w = 362436069;

	z = 36969 * (z & 65535) + (z >> 16);
	w = 18000 * (w & 65535) + (w >> 16);
	return (z << 16) + w;
}

void io_rw_test(volatile unsigned int* ptr, unsigned int size)
{
	unsigned int i;
	unsigned int cmp[size];
	unsigned int res = 0;
	int* tmp = 0;

	for(i=0; i<size; i++) {
		cmp[i] = random();
	}

	for(i=0; i<size; i++) {
		ptr[i] = cmp[i]; 
	}

	for(i=0; i<size; i++) {
		if( cmp[i] != ptr[i] )
			res += 1;
	}

	if( res > 0 ) {
		*tmp = 0x0bad;
		*(tmp+1) = res;
	} else { 
		*tmp = 0x600d;
		*(tmp+3) = res;
	}
}


void start()
{
	io_rw_test(io_ram, 8);
}
