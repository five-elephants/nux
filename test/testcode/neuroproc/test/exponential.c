// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#include <stdio.h>
#include <math.h>

#include "../fxdpt.h"
#include "../exp.h"

int main()
{
	double xf;
	double yf;
	int32_t xd;
	int32_t yd;
	double yerr;

	for(xf=-11.0; xf<=11.0; xf += 0.1) {
		xd = FP(xf);

		yf = exp(xf);
		yd = exp_6b(xd);

		yerr = fabs(yf - INV_FP(yd));
		printf("xf=%f yf=%f xd=%f yd=%f  ->  yerr=%f\n",
			xf, yf, INV_FP(xd), INV_FP(yd), yerr);
	}

	return 0;
}
