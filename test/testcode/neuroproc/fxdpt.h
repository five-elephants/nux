#ifndef FXDPT_H__
#define FXDPT_H__

#include <stdint-gcc.h>

/** INV_SCALE 0x10000 is the 16.16 fixedpoint representation
 * MAX:       65536
 * MIN:      -65536
 * precision:    15.26e-6
 * */
#define INV_SCALE  0x10000
#define INV_SCALE_16 0x10
//#define INV_SCALE 16777216/128
#define SCALE (1.0/(double)INV_SCALE)
#define SCALE_16 (1.0/(double)INV_SCALE)

#define FP(x) ((int32_t)(INV_SCALE * (x)))
#define FP16(x) ((int16_t)(INV_SCALE_16 * (x)))
#define INV_FP(x) ((double)x*SCALE)
#define FP_MUL(x,y) (x*y / INV_SCALE)

static int16_t fxdpt_32_to_16_bits(const int32_t x)
{
	if( INV_SCALE_16 < INV_SCALE )
		return (int16_t)( x / (INV_SCALE / INV_SCALE_16) );
	else
		return (int16_t)( x * (INV_SCALE_16 / INV_SCALE) );
}

#endif

