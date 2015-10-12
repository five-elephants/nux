#ifndef S2PP_LED_H__
#define S2PP_LED_H__

static void led(const char nibble)
{
	asm("mtspr 0b0001000010, %0" 
			: /* no output */
			: "r"(nibble)
			: /* no clobber */);
}

#endif

