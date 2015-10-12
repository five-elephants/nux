#!/bin/sh

BASEDIR=`dirname $0`/../..

. $BASEDIR/support/sh2ju++.sh

cd $BASEDIR/verification/sim_model
export NO_COLOR_OUTPUT=y
juLogSuiteOpen "plt_test"
juLog -name="program_test" -error="Some programs failed" vsim -c -L lib/DW -voptargs="+acc" -sv_seed random work.Program_test -l plt.transcript -do "run -all ; exit -f"

juLogSuiteClose
