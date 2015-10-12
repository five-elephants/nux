onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/master_word_in
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/master_word_out
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/next_master_word_in
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/master_ser_line
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/slave_word_in
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/slave_word_out
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/next_slave_word_in
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/slave_ser_line
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/master_ser_start
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/master_ser_valid
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/slave_ser_start
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/slave_ser_valid
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/master_des_ready
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/master_rx_ready
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/slave_des_ready
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/slave_rx_ready
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/master_des_out
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/slave_des_out
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/cmd_accepted
add wave -noupdate -radix hexadecimal /Bus_serial_test/uut/resp_accepted
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/Clk
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/MReset_n
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/MAddr
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/MCmd
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/MData
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/MDataValid
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/MRespAccept
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/SCmdAccept
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/SData
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/SDataAccept
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/SResp
add wave -noupdate -expand -group in -radix hexadecimal /Bus_serial_test/in/MByteEn
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/Clk
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/MReset_n
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/MAddr
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/MCmd
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/MData
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/MDataValid
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/MRespAccept
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/SCmdAccept
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/SData
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/SDataAccept
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/SResp
add wave -noupdate -expand -group out -radix hexadecimal /Bus_serial_test/out/MByteEn
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1110 ps} 0}
configure wave -namecolwidth 199
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 2
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ps} {496070 ps}
