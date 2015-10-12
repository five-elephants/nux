onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -format Logic /Tag_shiftreg_test/clk
add wave -noupdate -format Logic /Tag_shiftreg_test/reset
add wave -noupdate -divider Internals
add wave -noupdate -format Literal -expand /Tag_shiftreg_test/uut/tags
add wave -noupdate -format Literal /Tag_shiftreg_test/uut/data
add wave -noupdate -format Literal /Tag_shiftreg_test/uut/valids
add wave -noupdate -format Literal {/Tag_shiftreg_test/uut/g_testport[0]/cmp}
add wave -noupdate -format Literal {/Tag_shiftreg_test/uut/g_testport[1]/cmp}
add wave -noupdate -format Literal {/Tag_shiftreg_test/uut/g_testport[2]/cmp}
add wave -noupdate -format Logic /Tag_shiftreg_test/intf/shift
add wave -noupdate -format Literal /Tag_shiftreg_test/intf/tag
add wave -noupdate -format Literal /Tag_shiftreg_test/intf/datain
add wave -noupdate -format Logic /Tag_shiftreg_test/intf/tag_valid
add wave -noupdate -format Literal -expand /Tag_shiftreg_test/intf/test
add wave -noupdate -format Literal -expand /Tag_shiftreg_test/intf/found
add wave -noupdate -format Literal -expand /Tag_shiftreg_test/intf/index
add wave -noupdate -format Literal /Tag_shiftreg_test/uut/dataout_i
add wave -noupdate -format Literal /Tag_shiftreg_test/intf/dataout
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {136994 ps} 0}
configure wave -namecolwidth 285
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 3
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
WaveRestoreZoom {68847 ps} {264621 ps}
