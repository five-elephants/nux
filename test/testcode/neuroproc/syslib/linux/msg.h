#ifndef LINUX_MSG_H__
#define LINUX_MSG_H__

#include <stdint.h>

extern void __send_msg(const uint32_t rank, const uint32_t addr, const uint32_t data);

extern uint32_t __recv_msg(const uint32_t rank, const uint32_t addr);

/** Query the empty flag of the message queue to determine if messages can be
 * received. */
extern uint32_t __msg_waiting(const uint32_t rank, uint32_t addr);


static void send_msg(const uint32_t addr, const uint32_t data)
	{ __send_msg(MSG_RANK, addr, data); }

static uint32_t recv_msg(const uint32_t addr)
	{ return __recv_msg(MSG_RANK, addr); }	

/** Query the empty flag of the message queue to determine if messages can be
 * received. */
static uint32_t msg_waiting(uint32_t addr)
	{ return __msg_waiting(MSG_RANK, addr); }

#endif
