vsim -L DW -voptargs="+acc=aprm +cover -L DW" -sv_seed random -coverage -assertdebug work.Test_read_cache
# vsim -L DW -L xilinxcorelib_ver -L unisims_ver -voptargs="-O5 +acc=aprm +cover -L DW -L xilinxcorelib_ver -L unisims_ver" -sv_seed random -coverage -assertdebug work.Sequence_test work.glbl
