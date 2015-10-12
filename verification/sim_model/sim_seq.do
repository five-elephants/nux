vsim -L lib/DW -voptargs=+acc -novopt -sv_seed random work.Sequence_test

# vsim -L DW -voptargs="-O5 +acc=aprm +cover -L DW" -sv_seed random -coverage -assertdebug work.Sequence_test
# vsim -L DW -L xilinxcorelib_ver -L unisims_ver -voptargs="+acc=aprm +cover -L DW -L xilinxcorelib_ver -L unisims_ver" -sv_seed random -coverage -assertdebug work.Sequence_test work.glbl
