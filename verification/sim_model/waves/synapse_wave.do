onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -height 18 -expand -group syn_io_a_if /Program_test/syn_io_a_if/busy
add wave -noupdate -height 18 -expand -group syn_io_a_if /Program_test/syn_io_a_if/start
add wave -noupdate -height 18 -expand -group syn_io_a_if /Program_test/syn_io_a_if/op
add wave -noupdate -height 18 -expand -group syn_io_a_if /Program_test/syn_io_a_if/client2syn_valid
add wave -noupdate -height 18 -expand -group syn_io_a_if /Program_test/syn_io_a_if/client2syn_data
add wave -noupdate -height 18 -expand -group syn_io_a_if /Program_test/syn_io_a_if/client2syn_patterns
add wave -noupdate -height 18 -expand -group syn_io_a_if /Program_test/syn_io_a_if/syn2client_valid
add wave -noupdate -height 18 -expand -group syn_io_a_if /Program_test/syn_io_a_if/syn2client_data
add wave -noupdate -height 18 -expand -group syn_io_a_if /Program_test/syn_io_a_if/syn2client_channel
add wave -noupdate -height 18 -expand -group syn_io_a_if /Program_test/syn_io_a_if/syn2client_pat_ctr
add wave -noupdate -height 18 -expand -group syn_io_b_if /Program_test/syn_io_b_if/busy
add wave -noupdate -height 18 -expand -group syn_io_b_if /Program_test/syn_io_b_if/start
add wave -noupdate -height 18 -expand -group syn_io_b_if /Program_test/syn_io_b_if/op
add wave -noupdate -height 18 -expand -group syn_io_b_if /Program_test/syn_io_b_if/client2syn_valid
add wave -noupdate -height 18 -expand -group syn_io_b_if /Program_test/syn_io_b_if/client2syn_data
add wave -noupdate -height 18 -expand -group syn_io_b_if /Program_test/syn_io_b_if/client2syn_patterns
add wave -noupdate -height 18 -expand -group syn_io_b_if /Program_test/syn_io_b_if/syn2client_valid
add wave -noupdate -height 18 -expand -group syn_io_b_if /Program_test/syn_io_b_if/syn2client_data
add wave -noupdate -height 18 -expand -group syn_io_b_if /Program_test/syn_io_b_if/syn2client_channel
add wave -noupdate -height 18 -expand -group syn_io_b_if /Program_test/syn_io_b_if/syn2client_pat_ctr
add wave -noupdate -divider {FUB Synapse}
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/inst
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/resbus
add wave -noupdate -radix hexadecimal -expand -subitemconfig {{/Program_test/uut/gen_fub_synapse/fub_synaspe/lut[0]} {-height 17 -radix hexadecimal} {/Program_test/uut/gen_fub_synapse/fub_synaspe/lut[1]} {-height 17 -radix hexadecimal}} /Program_test/uut/gen_fub_synapse/fub_synaspe/lut
add wave -noupdate -radix hexadecimal -expand -subitemconfig {{/Program_test/uut/gen_fub_synapse/fub_synaspe/svr[0]} {-height 17 -radix hexadecimal -expand} {/Program_test/uut/gen_fub_synapse/fub_synaspe/svr[0][0]} {-height 17 -radix hexadecimal} {/Program_test/uut/gen_fub_synapse/fub_synaspe/svr[0][1]} {-height 17 -radix hexadecimal} {/Program_test/uut/gen_fub_synapse/fub_synaspe/svr[0][2]} {-height 17 -radix hexadecimal} {/Program_test/uut/gen_fub_synapse/fub_synaspe/svr[0][3]} {-height 17 -radix hexadecimal} {/Program_test/uut/gen_fub_synapse/fub_synaspe/svr[1]} {-height 17 -radix hexadecimal -expand} {/Program_test/uut/gen_fub_synapse/fub_synaspe/svr[1][0]} {-height 17 -radix hexadecimal} {/Program_test/uut/gen_fub_synapse/fub_synaspe/svr[1][1]} {-height 17 -radix hexadecimal} {/Program_test/uut/gen_fub_synapse/fub_synaspe/svr[1][2]} {-height 17 -radix hexadecimal} {/Program_test/uut/gen_fub_synapse/fub_synaspe/svr[1][3]} {-height 17 -radix hexadecimal}} /Program_test/uut/gen_fub_synapse/fub_synaspe/svr
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/svr_switch
add wave -noupdate -radix hexadecimal -expand -subitemconfig {/Program_test/uut/gen_fub_synapse/fub_synaspe/ir.i {-height 17 -radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.b {-height 17 -radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.d {-height 17 -radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.xo {-height 17 -radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.x {-height 17 -radix hexadecimal -expand} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.x.opcd {-radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.x.rt {-radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.x.ra {-radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.x.rb {-radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.x.xo {-radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.x.rc {-radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.m {-height 17 -radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.xfx {-height 17 -radix hexadecimal} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir.xl {-height 17 -radix hexadecimal}} /Program_test/uut/gen_fub_synapse/fub_synaspe/ir
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/aa
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/bb
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/cc
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/map_res
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/select_res
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/next_lut_sel
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/lut_sel
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/next_select_state
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/select_state
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/next_save_select_state
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/save_select_state
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/next_output_map
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/output_map
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/next_save_lut
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/save_lut
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/v_aa
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/v_bb
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/front_we
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/front_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/swap
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/next_mtvr_index
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/mtvr_index
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/mtvr_res
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_synapse/fub_synaspe/mfvr_res
add wave -noupdate /Program_test/uut/gen_fub_synapse/fub_synaspe/next_start_seq
add wave -noupdate /Program_test/uut/gen_fub_synapse/fub_synaspe/start_seq
add wave -noupdate /Program_test/uut/gen_fub_synapse/fub_synaspe/synapse_busy
add wave -noupdate -divider Frontend
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/ext_hold
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/io_pipe_empty
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/ls_pipe_empty
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/ctrl
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/bctrl
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/ictrl
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/opf_predec
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/opf_issue
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/issue_slots
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/predicted_taken
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/sleeping
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/mon_inst
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/mon_pc
add wave -noupdate -radix hexadecimal -expand -subitemconfig {/Program_test/uut/frontend/fst_d.pc {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.npc {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.inst {-height 17 -radix hexadecimal -expand} /Program_test/uut/frontend/fst_d.inst.i {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.b {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.d {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.xo {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.x {-height 17 -radix hexadecimal -expand} /Program_test/uut/frontend/fst_d.inst.x.opcd {-radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.x.rt {-radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.x.ra {-radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.x.rb {-radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.x.xo {-radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.x.rc {-radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.m {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.xfx {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.inst.xl {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.predicted_taken {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.valid {-height 17 -radix hexadecimal} /Program_test/uut/frontend/fst_d.trans_cmplt {-height 17 -radix hexadecimal}} /Program_test/uut/frontend/fst_d
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fst_stream
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fst_stream_d
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/seq_ctr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/hold_stream
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/schedule_stall
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/predec
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/predec_d
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_ready
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/issue_slots_i
add wave -noupdate -radix hexadecimal -expand -subitemconfig {{/Program_test/uut/frontend/ready[0]} {-height 17 -radix hexadecimal} {/Program_test/uut/frontend/ready[1]} {-height 17 -radix hexadecimal} {/Program_test/uut/frontend/ready[2]} {-height 17 -radix hexadecimal} {/Program_test/uut/frontend/ready[3]} {-height 17 -radix hexadecimal} {/Program_test/uut/frontend/ready[4]} {-height 17 -radix hexadecimal} {/Program_test/uut/frontend/ready[5]} {-height 17 -radix hexadecimal} {/Program_test/uut/frontend/ready[6]} {-height 17 -radix hexadecimal} {/Program_test/uut/frontend/ready[7]} {-height 17 -radix hexadecimal}} /Program_test/uut/frontend/ready
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/issue
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/mc_hold
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/pipe_empty_track
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/pipe_empty
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/ignore_inst
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/csync
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/int_csync
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/disable_wb
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/jumping
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/jumping_d
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/eff_bctrl
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/div_stall
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/ls_stall
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/io_stall
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/stalled_by_fubs
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/about_to_halt
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/ext_int_save_pc
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/del_commit
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/del_com_ls
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/del_com_io
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/issue_slots_i__FUB_ID_DIV
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/issue_slots_i__FUB_ID_IO
add wave -noupdate -radix hexadecimal /Program_test/uut/wbc_gpr/dest
add wave -noupdate -radix hexadecimal /Program_test/uut/wbc_gpr/src
add wave -noupdate -radix hexadecimal /Program_test/uut/wbc_gpr/we
add wave -noupdate -radix hexadecimal /Program_test/uut/res
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file/gpr
add wave -noupdate -divider {New Divider}
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/clk
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/reset
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal -expand -subitemconfig {/Program_test/uut/gen_fub_never/fub_never/inst.ir {-height 17 -radix hexadecimal} /Program_test/uut/gen_fub_never/fub_never/inst.pc {-height 17 -radix hexadecimal} /Program_test/uut/gen_fub_never/fub_never/inst.npc {-height 17 -radix hexadecimal} /Program_test/uut/gen_fub_never/fub_never/inst.valid {-height 17 -radix hexadecimal} /Program_test/uut/gen_fub_never/fub_never/inst.thread {-height 17 -radix hexadecimal}} /Program_test/uut/gen_fub_never/fub_never/inst
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/resbus
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal -expand -subitemconfig {{/Program_test/uut/gen_fub_never/fub_never/lut[0]} {-height 17 -radix hexadecimal} {/Program_test/uut/gen_fub_never/fub_never/lut[1]} {-height 17 -radix hexadecimal}} /Program_test/uut/gen_fub_never/fub_never/lut
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/ir
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/aa
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/bb
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/cc
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/map_res
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/select_res
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/next_lut_sel
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/lut_sel
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/next_select_state
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/select_state
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/next_save_select_state
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/save_select_state
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/next_output_map
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/output_map
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/next_save_lut
add wave -noupdate -height 18 -group {FUB Never} -radix hexadecimal /Program_test/uut/gen_fub_never/fub_never/save_lut
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1500960 ps} 0}
configure wave -namecolwidth 220
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
WaveRestoreZoom {0 ps} {2409760 ps}
