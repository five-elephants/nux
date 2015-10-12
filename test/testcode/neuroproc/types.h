#ifndef TYPES_H__
#define TYPES_H__

#include <stdint-gcc.h>

typedef union {
	uint32_t word;
	struct {
		uint16_t padding;
		uint8_t id;
		int8_t weight;
	} event;

	struct {
		uint8_t padding;
		uint8_t row;
		uint8_t col;
		int8_t change;
	} update;
} msg_t;

#endif

