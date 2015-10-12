#ifndef MSG_H__
#define MSG_H__

#ifdef PLATFORM_LINUX
#	include <linux/msg.h>
#else
#	include <s2pp/msg.h>
#endif

#endif

