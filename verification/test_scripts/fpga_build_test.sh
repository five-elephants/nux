#!/bin/sh

. `dirname $0`/support/sh2ju.sh

juLogClean

cd fpga
juLog -name="synplify"          make
juLog -name="bitfile"           make bit
