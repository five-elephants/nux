onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/clk
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/reset
add wave -noupdate /Frontend_test_single/cycle
add wave -noupdate -expand /Frontend_test_single/uut/ctrl
add wave -noupdate -radix hexadecimal -expand -subitemconfig {/Frontend_test_single/uut/bctrl.jump {-height 18 -radix hexadecimal} /Frontend_test_single/uut/bctrl.jump_vec {-height 18 -radix hexadecimal} /Frontend_test_single/uut/bctrl.fb_taken {-height 18 -radix hexadecimal} /Frontend_test_single/uut/bctrl.fb_not_taken {-height 18 -radix hexadecimal} /Frontend_test_single/uut/bctrl.fb_pc {-height 18 -radix hexadecimal}} /Frontend_test_single/uut/bctrl
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/issue_fxdpt
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/issue_branch
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/issue_ls
add wave -noupdate -radix hexadecimal -expand -subitemconfig {/Frontend_test_single/uut/fst.pc {-height 18 -radix hexadecimal} /Frontend_test_single/uut/fst.npc {-height 18 -radix hexadecimal} /Frontend_test_single/uut/fst.inst {-height 18 -radix hexadecimal} /Frontend_test_single/uut/fst.predicted_taken {-height 18 -radix hexadecimal} /Frontend_test_single/uut/fst.valid {-height 18 -radix hexadecimal} /Frontend_test_single/uut/fst.trans_cmplt {-height 18 -radix hexadecimal}} /Frontend_test_single/uut/fst
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/hold_stream
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/schedule_stall
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/predec
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_ready
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/fub_fxdpt_ready
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/fub_branch_ready
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/fub_ls_ready
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/issue_fxdpt_i
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/issue_branch_i
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/issue_ls_i
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/issue
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/shreg_stages
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/clk
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/reset
add wave -noupdate -radix hexadecimal -expand -subitemconfig {/Frontend_test_single/uut/inst_track/fst.pc {-height 18 -radix hexadecimal} /Frontend_test_single/uut/inst_track/fst.npc {-height 18 -radix hexadecimal} /Frontend_test_single/uut/inst_track/fst.inst {-height 18 -radix hexadecimal} /Frontend_test_single/uut/inst_track/fst.predicted_taken {-height 18 -radix hexadecimal} /Frontend_test_single/uut/inst_track/fst.valid {-height 18 -radix hexadecimal} /Frontend_test_single/uut/inst_track/fst.trans_cmplt {-height 18 -radix hexadecimal}} /Frontend_test_single/uut/inst_track/fst
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/predec
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/ready
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/issue
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/shift
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/ra
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/rb
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/rt
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/dest
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/src
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/occupied
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/test
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/found
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/index
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/out_dest
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/out_src_bits
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/out_src
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/out_valid
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/stage
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/clk
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/reset
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/shift
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/dest
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/src
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/stage
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/we
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/occupied
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/test
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/found
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/index
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/out_dest
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/out_src
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/out_valid
add wave -noupdate -radix hexadecimal /Frontend_test_single/uut/inst_track/track_gpr/gpr_tracker_a/shreg
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1802081 ps} 0}
configure wave -namecolwidth 241
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
WaveRestoreZoom {0 ps} {4200 ns}
