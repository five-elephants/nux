/*********************************************************
led(x) as led function with x as 4bit number-code for the 4 leds
**********************************************************/


void led(char nibble)
{
        asm("mtspr 0b0001000010, %0"
                        : /* no output */
                        : "r"(nibble)
                        : /* no clobber */);
}

