// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



typedef unsigned long long uint64_t;
typedef unsigned short int uint16_t;
typedef unsigned int uint32_t;
typedef unsigned char uint8_t;

#include "isr.h"
#include "spr.h"
#include "../neuroproc/syslib/s2pp/time_base.h"
#include "led.h"

#define WAIT asm volatile (".byte 0x7c, 0x00, 0x00, 0x7c");

#define EV_DEC (0x1)
#define EV_FIT (0x2)

#define MEGA (1000000)
#define TICKS_PER_SEC (100 * MEGA)
#define DEC_INTERVAL (TICKS_PER_SEC/10)
#define PWM_MAX (65536)
#define PWM_MIN (0)
#define PWM_STEP (PWM_MAX / 100)

volatile unsigned int events;
volatile unsigned int dec_counter;
volatile unsigned int fit_counter;
unsigned char led_var;
volatile unsigned int srr0_save;
volatile unsigned int srr1_save;
uint32_t pwm;

static void wait() 
{ 
	asm volatile (
		"nop\n"
		"nop\n"
		".byte 0x7c, 0x00, 0x00, 0x7c\n"
	); 
}
/*static void wait() { asm ("wait"); }*/

void start()
{
	events = 0;
	dec_counter = 0;
	fit_counter = 0;
	pwm = PWM_MIN;

	led_var = 0x2;

	led_with_enable(led_var, 0x3);

	// set DEC & FIT
	clear_tsr(TSR_DIS | TSR_FIS);
	set_dec(DEC_INTERVAL);
	set_tcr(TCR_DIE);
	/*set_tcr(TCR_FIE);*/
	set_fit_period(TCR_FP_BIT_16);

	// set the external enable bit 
	set_msr(get_msr() | MSR_EE);	

	while( 1 ) {
		if( events & EV_DEC ) {
			++dec_counter;
			events &= ~EV_DEC;

			// disable LED
			led_var &= ~0x1;
			led_with_enable(led_var, 0x3);

			led_var ^= 0x2;
			led_with_enable(led_var, 0x3);
		}

		/*if( events & EV_FIT ) {*/
		if( get_tsr() & TSR_FIS ) {
			clear_tsr(TSR_FIS);
			++fit_counter;
			events &= ~EV_FIT;

			// enable LED
			led_var |= 0x1;
			led_with_enable(led_var, 0x3);

			// do pulse width modulation
			if( pwm < 2*PWM_MAX ) {
				pwm += PWM_STEP;

				if( pwm < PWM_MAX )
					set_dec(pwm);
				else
					set_dec(2*PWM_MAX - pwm);
			} else if( pwm >= 2*PWM_MAX ) {
				pwm = PWM_MIN;
				set_dec(pwm);
			}

			set_dec(3000);

			/*led_var = led_var ^ 0x1;*/
			/*led_with_enable(led_var, 0x3);*/
		}

		/*wait();*/
	}
}

//asm (
//	".global isr_dec\n"
//	"isr_dec:\n"
//	"	stw 1, 0x3f00(0)\n"   // save stack pointer
//	"	li 1, 0x3ff8\n"       // load interrupt stack pointer
//	"	bl isr_dec_func\n"    // call actual service routine
//	"	lwz 1, 0x3f00(0)\n"   // restore stack pointer
//	"	rfi\n"
//);


ISR_DEC
{
	uint32_t srr0;

	/*asm volatile (
		"lis 2, 0x0800\n"       // clear TSR.DIS bit
		"mtspr 336, 2\n"

		"lwz 2, dec_counter@l(0)\n"
		"addi 2, 2, 1\n"
		"stw 2, dec_counter@l(0)\n"

		"lis 2, 0x2386\n"         // load new decrementer value
		"ori 2, 2, 0x3d00\n"
		"mtdec 2\n"
		:  [> no output <]
		:  [> no input <]
		: "2" [> clobber <]
	);*/

	/*wait();*/

	// clear interrupt bit
	clear_tsr(TSR_DIS);

	/*if( dec_counter < 100 )*/
		/*set_dec(DEC_INTERVAL);*/

	events |= EV_DEC;	
	/*dec_counter += 1;*/

	srr0 = get_srr0();
	srr0 += 4;
	set_srr0(srr0);
	srr1_save = get_srr1();

	/*asm (*/
		/*"	mfsrr0 2\n"*/
		/*"	stw 2, srr0_save@l(0)\n"*/
		/*"	addi 2, 2, 4\n"*/
		/*"	mtsrr0 2\n"*/
		/*"	mfsrr1 2\n"*/
		/*"	stw 2, srr1_save@l(0)\n"*/
		/*: : : "2"*/
	/*);*/

}

ISR_FIT
{
	uint32_t srr0;

	clear_tsr(TSR_FIS);

	events |= EV_FIT;

	srr0 = get_srr0();
	srr0 += 4;
	set_srr0(srr0);
}
