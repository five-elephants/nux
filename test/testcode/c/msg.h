#ifndef MSG_H__
#define MSG_H__

#include <stdint-gcc.h>

static void send_msg(const uint32_t addr, const uint32_t data)
{
	static const uint32_t offset = 0;

	asm volatile("ecowx %0, %1, %2"
			: /* output */
			: "r"(data), "r"(addr), "r"(offset)/* input */
			: /* clobber */);
}

static uint32_t recv_msg(const uint32_t addr)
{
	uint32_t rv;
	static const uint32_t offset = 0;

	asm volatile("eciwx %0, %1, %2"
			: "=r"(rv)  /* output */
			: "r"(addr), "r"(offset) /* input */
			: /* clobber */);

	return rv;
}

/** Query the empty flag of the message queue to determine if messages can be
 * received. */
static uint32_t msg_waiting(uint32_t addr)
{
	uint32_t rv;
	static const uint32_t offset = 4;

	asm volatile("eciwx %0, %1, %2"
			: "=r"(rv)  /* output */
			: "r"(addr), "r"(offset) /* input */
			: /* clobber */);

	return (rv == 1) ? 0 : 1;
}

#endif
