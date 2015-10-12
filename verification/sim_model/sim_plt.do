vsim -L lib/DW -voptargs="+acc" work.Program_test 

# vsim -L DW -novopt work.Program_test
#vsim -L DW -L xilinxcorelib_ver -L unisims_ver -voptargs="-O5 +acc=aprm +cover -L DW -L xilinxcorelib_ver -L unisims_ver" -sv_seed random -coverage -assertdebug work.Program_test work.glbl
