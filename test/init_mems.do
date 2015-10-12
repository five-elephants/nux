onerror resume
add mem /Pu_test/uut/inst_fetch/imem -a hexadecimal -d hexadecimal
add mem /Pu_test/uut/load_store/mem -a hexadecimal -d hexadecimal

mem load -i testcode/interlocks_code.mem -format hex /Pu_test/uut/inst_fetch/imem
mem load -i testcode/load_add_store.mem -format mti /Pu_test/uut/load_store/mem
