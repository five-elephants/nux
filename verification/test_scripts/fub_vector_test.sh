#!/bin/sh

BASEDIR=`dirname $0`/../..

. $BASEDIR/support/sh2ju++.sh

cd $BASEDIR/verification/sim_model
export NO_COLOR_OUTPUT=y
juLogSuiteOpen "fub_vector_test"
juLog -name="fub_vector_test" -error="ERRORS DETECTED" vsim -c -L lib/DW -voptargs="+noacc" -sv_seed random work.Signoff_vector_test -l vector.transcript -do "run -all ; coverage report -details -file fcover_report.txt ; exit -f"

juLogSuiteClose
