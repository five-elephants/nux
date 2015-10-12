#ifndef LED_H__
#define LED_H__

static void led(const char nibble)
{
	asm("mtspr 0b0001000010, %0" 
			: /* no output */
			: "r"(nibble)
			: /* no clobber */);
}

static void led_with_enable(char nibble, char oe)
{
	asm(
    "mtspr 0b0001000011, %0\n"
    "mtspr 0b0001000010, %1\n" 
			: /* no output */
			: "r"(oe), "r"(nibble)
			: /* no clobber */
  );
}

#endif

