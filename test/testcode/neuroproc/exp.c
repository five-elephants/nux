// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


//#include <stdlib.h>
//#include <stdio.h>
//#include <math.h>

#include "fxdpt.h"
#include <stdint-gcc.h>

/** calculate the first 6 terms of the series expansion of the exponential
 * function.
 *
 * exp(x) = 1 + x + x**2/2 + x**3/6 + x**4/24 + x**5/120     + O(x**6)
 * exp(C*y) = exp(C) + exp(y) = exp(x)
 * */
int32_t exp_6(int32_t x)
{
	int32_t x2;
	int32_t x3;
	int32_t x4;
	int32_t x5;

	/* avoid overflow problems for the multiplication */
	if( (x < FP(1.0)) && (x > FP(-1.0)) ) {
		x2 = (x  * x ) / INV_SCALE;
		x3 = (x2 * x ) / INV_SCALE;
		x4 = (x2 * x2) / INV_SCALE;
		x5 = (x3 * x2) / INV_SCALE;
	} else {
		x2 = x  * (x  / INV_SCALE);
		x3 = x2 * (x  / INV_SCALE);
		x4 = x2 * (x2 / INV_SCALE);
		x5 = x3 * (x2 / INV_SCALE);
	}

	return FP(1.0) + x + (x2/2) + (x3/6) + (x4/24) + (x5/120);
	/*return 1 + x + FP_MUL(FP(0.5),x2)*/
		/*+ FP_MUL(FP(0.166666666667),x3)*/
		/*+ FP_MUL(FP(0.041666666667),x4)*/
		/*+ FP_MUL(FP(0.008333333333),x5);*/
}

/** Can not handle x > 10 */
int32_t exp_6b(int32_t x)
{
	// exponential function for integers from -11 to 11
	static const int32_t lut[22] = {
		FP(0.000017), FP(0.000045), FP(0.000123), FP(0.000335),
		FP(0.000912), FP(0.002479), FP(0.006738), FP(0.018316),
		FP(0.049787), FP(0.135335), FP(0.367879), 
		FP(1.000000),
		FP(2.718282), FP(7.389056), FP(20.085537), FP(54.598150),
		FP(148.413159), FP(403.428793), FP(1096.633158), 
		FP(2980.957987), FP(8103.083928), FP(22026.465795)
	};

	int32_t ik;
	int32_t fk;
	int32_t res_i;
	int32_t res_f;
	int32_t x2;
	int32_t x3;
	int32_t x4;
	int32_t x5;

	ik = x / INV_SCALE;         // integer part
	fk = x - (ik * INV_SCALE);  // fractional part

	// adjust exponents to stay in fast convergence range [-0.5, 0.5]
	if( fk > FP(0.5) ) {
		++ik;
		fk -= FP(1.0);
	} else if( fk < FP(-0.5) ) {
		--ik;
		fk += FP(1.0);
	}

	// calculate exponential for integer part
	if( ik > 11 )
		res_i = 65535;
	else if( ik < -11 )
		res_i = -65535;
	else
		res_i = lut[ik+11];

	// calculate exponential for the fractional part
	x2 = (fk * fk) / INV_SCALE;
	x3 = (x2 * fk) / INV_SCALE;
	x4 = (x2 * x2) / INV_SCALE;
	x5 = (x3 * x2) / INV_SCALE;

	res_f = FP(1.0) + fk + (x2/2) + (x3/6) + (x4/24) + (x5/120);

	// combine results
	/*printf("exp_6b: ik=%d, fk=%f, res_i=%f res_f=%f\n",*/
		/*ik, INV_FP(fk), INV_FP(res_i), INV_FP(res_f));*/
	return ((int64_t)res_i * (int64_t)res_f) / INV_SCALE;
}

int32_t exp_n(int32_t x, const uint32_t n)
{
	int32_t i;
	int32_t xto;
	int32_t coeff;
	int32_t rv;

	rv = FP(1.0) + x; 
	coeff = 1;
	xto = x;

	for(i=2; i<n; i++) {
		coeff = (i * coeff);  // faculty of i
		
		if( (x < FP(1.0)) && (x > FP(-1.0)) )
			xto = (xto * x) / INV_SCALE;
		else
			xto = xto * (x / INV_SCALE);

		rv += xto / coeff;
	}
			
	return rv;
}
