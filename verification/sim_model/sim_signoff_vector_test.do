transcript file "signoff_vector_test.transcript"

add wave -r /*
dataset snapshot -enable -file signoff_vector_test.wlf -time {10 ms}
run -all
dataset save sim signoff_vector_test.wlf

