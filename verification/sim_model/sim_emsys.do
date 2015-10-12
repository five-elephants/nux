# vsim -L DW -L unisims_ver -L xilinxcorelib_ver -voptargs="+acc=aprm -L DW -L unisims_ver -L xilinxcorelib_ver" -coverage -assertdebug  work.Emsys_top_test work.glbl
vsim -L DW -L unisims_ver -L xilinxcorelib_ver  -novopt -assertdebug  work.Emsys_top_test work.glbl
