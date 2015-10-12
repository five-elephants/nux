onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal /Inst_stream_test/clk
add wave -noupdate -radix hexadecimal /Inst_stream_test/reset
add wave -noupdate -radix hexadecimal /Inst_stream_test/jump
add wave -noupdate -radix hexadecimal /Inst_stream_test/jump_vec
add wave -noupdate -radix hexadecimal /Inst_stream_test/fb_taken
add wave -noupdate -radix hexadecimal /Inst_stream_test/fb_not_taken
add wave -noupdate -radix hexadecimal /Inst_stream_test/fb_pc
add wave -noupdate -radix hexadecimal /Inst_stream_test/trans_cmplt
add wave -noupdate -radix hexadecimal /Inst_stream_test/pc
add wave -noupdate -radix hexadecimal /Inst_stream_test/npc
add wave -noupdate -radix hexadecimal /Inst_stream_test/inst
add wave -noupdate -radix hexadecimal /Inst_stream_test/predicted_taken
add wave -noupdate -radix hexadecimal /Inst_stream_test/valid
add wave -noupdate -divider {New Divider}
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/clk
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/reset
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/addr
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/jump
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/jump_vec
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/taken
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/not_taken
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/pc
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/predict_taken
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/predict_target
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/valids
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/counts
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/targets
add wave -noupdate -radix hexadecimal /Inst_stream_test/uut/bcache/index
add wave -noupdate -divider {New Divider}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {6230000 ps} 0} {{Cursor 2} {2475189 ps} 0}
configure wave -namecolwidth 231
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
WaveRestoreZoom {6104451 ps} {6328436 ps}
