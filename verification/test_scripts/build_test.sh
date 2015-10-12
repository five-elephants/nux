#!/bin/sh

BASEDIR=`dirname $0`/../..

. $BASEDIR/support/sh2ju++.sh

cd $BASEDIR/verification/sim_model

juLogSuiteOpen "build_test"

export NO_COLOR_OUTPUT=y
juLog -name="clean"          make clean
juLog -name="build"          make
juLog -name="elaborate seq"  vsim -novopt -L lib/DW work.Sequence_test -elab seq.elab
juLog -name="elaborate plt"  vsim -novopt -L lib/DW work.Program_test -elab plt.elab

juLogSuiteClose
