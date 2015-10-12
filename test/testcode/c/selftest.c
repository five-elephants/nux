// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/** self-test operation to determine maximum clock frequency
 *
 * The program tests memory and functional units over potentially long 
 * runtimes to find rare single-bit errors, that may be introduced by faulty
 * SRAM bits (of the data memory) or timing-errors. */

typedef unsigned long long uint64_t;
typedef unsigned short int uint16_t;
typedef unsigned int uint32_t;
typedef unsigned char uint8_t;

#include "led.h"

#define RES_MEM_MASK    (0x000f)
#define RES_MEM_PASS    (0x0003)
#define RES_MEM_FAIL    (0x0002)
#define RES_MEM_RUNNING (0x0001)
#define RES_MEM_INIT    (0x0000)

#define RES_FXD_MASK    (0x00f0)
#define RES_FXD_PASS    (0x0030)
#define RES_FXD_FAIL    (0x0020)
#define RES_FXD_RUNNING (0x0010)
#define RES_FXD_INIT    (0x0000)

#define RES_MUL_MASK    (0x0f00)
#define RES_MUL_PASS    (0x0300)
#define RES_MUL_FAIL    (0x0200)
#define RES_MUL_RUNNING (0x0100)
#define RES_MUL_INIT    (0x0000)

volatile uint16_t result = RES_MEM_INIT;
volatile uint32_t error = 0;

static uint16_t set_result(uint16_t const r, uint16_t const mask)
{
	uint16_t rv = result;
	rv &= ~mask;
	rv |= (r & mask);
	return rv;
}

static void test_mem(const int loops,
		uint32_t volatile * const offset,
		uint32_t volatile * const end)
{
	static const uint32_t fixed[] = {
		0x00000000,
		0xffffffff,
		0xaaaaaaaa,
		0x55555555,
		0xf0f0f0f0,
		0x0f0f0f0f,
		0xff00ff00,
		0x00ff00ff,
		0xffff0000,
		0x0000ffff
	};
	static int const num_fixed = sizeof(fixed) / sizeof(uint32_t);

	int k;
	int i;
	uint32_t volatile *j;

	result = set_result(RES_MEM_RUNNING, RES_MEM_MASK);

	for(k=0; k<loops; k++) {
		for(i=0; i<num_fixed; i++) {
			for(j=offset; j<end; j++)
				(*j) = fixed[i];

			for(j=offset; j<end; j++)
				if( *j != fixed[i] )
					++error;
		}
	}

	if( error > 0 )
		result = set_result(RES_MEM_FAIL, RES_MEM_MASK);
	else
		result = set_result(RES_MEM_PASS, RES_MEM_MASK);
}

static void test_fixedpoint(int const loops)
{
	static int const invariant = 2147483647;

	int k;
	int a, b, res;
	uint32_t my_error = 0;

	a = 0;
	b = invariant;

	result = set_result(RES_FXD_RUNNING, RES_FXD_MASK);

	for(k=0; k<loops; k++) {
		res = a++ + b--;

		if( res != invariant )
			++my_error;
	}

	error += my_error;

	if( my_error > 0 )
		result = set_result(RES_FXD_FAIL, RES_FXD_MASK);
	else
		result = set_result(RES_FXD_PASS, RES_FXD_MASK);
}

static void test_mult(int const loops)
{
	static int const invariant = 10000;

	int i, k;
	int a, b, res;
	uint32_t my_error = 0;

	a = 1;
	b = invariant;

	result = set_result(RES_MUL_RUNNING, RES_MUL_MASK);

	for(k=0; k<loops; k++) {
		a = 1;
		b = invariant;

		for(i=0; i<5; i++) {
			res = a * b;
			a = a << 1;
			b = b >> 1;

			if( res != invariant )
				++my_error;
		}
	}

	error += my_error;

	if( my_error > 0 )
		result = set_result(RES_MUL_FAIL, RES_MUL_MASK);
	else
		result = set_result(RES_MUL_PASS, RES_MUL_MASK);
}

void start()
{
	while( 1 ) {
		led_with_enable(1, 3);

		test_mem(10, (uint32_t*)0x40000100, (uint32_t*)0x40003f00);	
		if( error > 0 )
			led_with_enable(3, 3);

		/*test_fixedpoint(0x7fffffff);*/
		test_fixedpoint(100000000);
		if( error > 0 )
			led_with_enable(3, 3);

		test_mult(1000);

		if( error > 0 )
			led_with_enable(1, 3);
		else
			led_with_enable(0, 3);
	}
}
