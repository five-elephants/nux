// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


/*typedef unsigned long long uint64_t;*/
/*typedef unsigned short int uint16_t;*/
/*typedef unsigned int uint32_t;*/

#include <stdint-gcc.h>

#include "isr.h"
#include "spr.h"
#include "led.h"

#define OP_ADD (1)
#define OP_SUB (2)
#define OP_MUL (3)
#define OP_DIV (4)

volatile int a, b;
volatile int op;
volatile int res;

static void wait() 
{ 
	asm volatile (
		"nop\n"
		"nop\n"
		".byte 0x7c, 0x00, 0x00, 0x7c\n"
	); 
}

void start()
{
	led_with_enable(0x2, 0x3);

	set_iccr(ICCR_DOORBELL_EN);   // enable doorbell interrupt
	set_msr(get_msr() & MSR_EE);  // enable external interrupts

	while( 1 ) {
		/*wait();*/
		switch( op ) {
			case OP_ADD:
				res = a + b;
				break;

			case OP_SUB:
				res = a - b;
				break;

			case OP_MUL:
				res = a * b;
				break;

			case OP_DIV:
				res = a / b;
				break;

			default:
				res = 0xffffffff;
		}
	}
}

ISR_DOORBELL
{
	led_with_enable(0x1, 0x3);

	switch( op ) {
		case OP_ADD:
			res = a + b;
			break;

		case OP_SUB:
			res = a - b;
			break;

		case OP_MUL:
			res = a * b;
			break;

		case OP_DIV:
			res = a / b;
			break;

		default:
			res = 0xffffffff;
	}
}
