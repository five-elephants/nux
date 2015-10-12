# vsim -L DW -voptargs="-O5 +acc=aprm +cover -L DW" -sv_seed random -coverage -assertdebug work.Bus_test
vsim -L DW -L xilinxcorelib_ver -L unisims_ver -voptargs="-O5 +acc=aprm +cover -L DW -L xilinxcorelib_ver -L unisims_ver" -sv_seed random -coverage -assertdebug work.Bus_test work.glbl
