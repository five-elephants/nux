#!/bin/sh

BASEDIR=`dirname $0`/../..
. $BASEDIR/support/sh2ju++.sh

cd $BASEDIR/target/emsys

export NO_COLOR_OUTPUT=y

juLogSuiteOpen "synthesis_emsys_test"
juLog -name="clean" make clean
juLog -name="synthesis" make
juLogSuiteClose
