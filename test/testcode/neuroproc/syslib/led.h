#ifndef LED_H__
#define LED_H__

#ifdef PLATFORM_LINUX
#	include <linux/led.h>
#else
#	include <s2pp/led.h>
#endif

#endif

