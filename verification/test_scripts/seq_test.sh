#!/bin/sh

#
# usage:
# [SVSEED=<seed>] ./seq_test.sh
# or
# [SVSEED=<seed>] ./seq_test.sh <program length> <use_cache> <use_dmem_bus> <bcache size>
# or: ./seq_test.sh
#
# <options> :
#    +define+OPT_DMEM_BUS          use bus memory interface
#    +define+USE_CACHE             use instruction cache
#    +define+OPT_BCACHE=<size>     use branch predictor with given size

BASEDIR=`dirname $0`/../..
DURATION="100 ms"
ERROR_MATCH="Error: mismatch"

. $BASEDIR/support/sh2ju++.sh

cd $BASEDIR/verification/sim_model
export NO_COLOR_OUTPUT=y

juLogSuiteOpen "seq_test"

if [ ! $SVSEED ] ; then
	SVSEED=random
fi

if test $# -gt 0 ; then

  XPARAM="+define+PROGRAM_LENGTH=$1 +define+OPT_BCACHE=$4"

  if test $2 -gt 0 ; then
    XPARAM= "+define+USE_CACHE $XPARAM"
  fi

  if test $3 -gt 0 ; then
    XPARAM="+define+OPT_DMEM_BUS $XPARAM"
  fi

  juLog -name="clean-$1" make clean
  juLog -name="build-$1" make VLOG_XPARAM=$XPARAM
  juLog -name="seq-$1" -error="$ERROR_MATCH" vsim -c -L lib/DW -voptargs="+acc" -novopt -sv_seed $SVSEED work.Sequence_test -do "run $DURATION ; exit -f"
else
  for i in 1 2 4 8 16 32 ; do
    juLog -name="clean-$i" make clean
    juLog -name="build-$i" make VLOG_XPARAM="+define+PROGRAM_LENGTH=$i"
    juLog -name="seq-$i" -error="$ERROR_MATCH" vsim -c -L lib/DW -voptargs="+acc" -novopt -sv_seed $SVSEED work.Sequence_test -do "run $DURATION ; exit -f"
  done
fi

juLogSuiteClose
