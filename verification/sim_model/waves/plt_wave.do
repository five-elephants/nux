onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal /Program_test/uut/OPT_BCACHE
add wave -noupdate -radix hexadecimal /Program_test/uut/OPT_MULTIPLIER
add wave -noupdate -radix hexadecimal /Program_test/uut/OPT_DIVIDER
add wave -noupdate -radix hexadecimal /Program_test/uut/OPT_IOBUS
add wave -noupdate -radix hexadecimal /Program_test/uut/OPT_IF_LATENCY
add wave -noupdate -radix hexadecimal /Program_test/uut/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/hold
add wave -noupdate -radix hexadecimal /Program_test/uut/gout
add wave -noupdate -radix hexadecimal /Program_test/uut/gin
add wave -noupdate -radix hexadecimal /Program_test/uut/goe
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend_control
add wave -noupdate -radix hexadecimal /Program_test/uut/branch_control
add wave -noupdate -radix hexadecimal /Program_test/uut/interrupt_control
add wave -noupdate -radix hexadecimal /Program_test/uut/opf_predec
add wave -noupdate -radix hexadecimal /Program_test/uut/opf_issue
add wave -noupdate -radix hexadecimal /Program_test/uut/issue
add wave -noupdate -radix hexadecimal -childformat {{{/Program_test/uut/res[0]} -radix hexadecimal} {{/Program_test/uut/res[1]} -radix hexadecimal} {{/Program_test/uut/res[2]} -radix hexadecimal -childformat {{{/Program_test/uut/res[2].res_a} -radix hexadecimal} {{/Program_test/uut/res[2].res_b} -radix hexadecimal} {{/Program_test/uut/res[2].cout} -radix hexadecimal} {{/Program_test/uut/res[2].ov} -radix hexadecimal} {{/Program_test/uut/res[2].crf} -radix hexadecimal} {{/Program_test/uut/res[2].msr} -radix hexadecimal} {{/Program_test/uut/res[2].valid} -radix hexadecimal}}} {{/Program_test/uut/res[3]} -radix hexadecimal} {{/Program_test/uut/res[4]} -radix hexadecimal} {{/Program_test/uut/res[5]} -radix hexadecimal} {{/Program_test/uut/res[6]} -radix hexadecimal} {{/Program_test/uut/res[7]} -radix hexadecimal}} -expand -subitemconfig {{/Program_test/uut/res[0]} {-height 18 -radix hexadecimal} {/Program_test/uut/res[1]} {-height 18 -radix hexadecimal} {/Program_test/uut/res[2]} {-height 18 -radix hexadecimal -childformat {{{/Program_test/uut/res[2].res_a} -radix hexadecimal} {{/Program_test/uut/res[2].res_b} -radix hexadecimal} {{/Program_test/uut/res[2].cout} -radix hexadecimal} {{/Program_test/uut/res[2].ov} -radix hexadecimal} {{/Program_test/uut/res[2].crf} -radix hexadecimal} {{/Program_test/uut/res[2].msr} -radix hexadecimal} {{/Program_test/uut/res[2].valid} -radix hexadecimal}} -expand} {/Program_test/uut/res[2].res_a} {-height 18 -radix hexadecimal} {/Program_test/uut/res[2].res_b} {-height 18 -radix hexadecimal} {/Program_test/uut/res[2].cout} {-height 18 -radix hexadecimal} {/Program_test/uut/res[2].ov} {-height 18 -radix hexadecimal} {/Program_test/uut/res[2].crf} {-height 18 -radix hexadecimal} {/Program_test/uut/res[2].msr} {-height 18 -radix hexadecimal} {/Program_test/uut/res[2].valid} {-radix hexadecimal} {/Program_test/uut/res[3]} {-height 18 -radix hexadecimal} {/Program_test/uut/res[4]} {-height 18 -radix hexadecimal} {/Program_test/uut/res[5]} {-height 18 -radix hexadecimal} {/Program_test/uut/res[6]} {-radix hexadecimal} {/Program_test/uut/res[7]} {-radix hexadecimal}} /Program_test/uut/res
add wave -noupdate -radix hexadecimal /Program_test/uut/opbus_i
add wave -noupdate -radix hexadecimal /Program_test/uut/predicted_taken
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/OPT_BCACHE
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/OPT_IF_LATENCY
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/USE_BCACHE
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/BCACHE_WIDTH
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/reset
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
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fst_d
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fst_stream
add wave -noupdate -radix hexadecimal -childformat {{/Program_test/uut/frontend/fst_stream_d.pc -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.npc -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst -radix hexadecimal -childformat {{/Program_test/uut/frontend/fst_stream_d.inst.i -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.b -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.d -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.xo -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.x -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {/Program_test/uut/frontend/fst_stream_d.inst.m -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.xfx -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.xl -radix hexadecimal}}} {/Program_test/uut/frontend/fst_stream_d.predicted_taken -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.valid -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.trans_cmplt -radix hexadecimal}} -expand -subitemconfig {/Program_test/uut/frontend/fst_stream_d.pc {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.npc {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst {-height 18 -radix hexadecimal -childformat {{/Program_test/uut/frontend/fst_stream_d.inst.i -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.b -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.d -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.xo -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.x -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {/Program_test/uut/frontend/fst_stream_d.inst.m -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.xfx -radix hexadecimal} {/Program_test/uut/frontend/fst_stream_d.inst.xl -radix hexadecimal}} -expand} /Program_test/uut/frontend/fst_stream_d.inst.i {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.b {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.d {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.xo {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.x {-height 18 -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}} -expand} /Program_test/uut/frontend/fst_stream_d.inst.x.opcd {-radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.x.rt {-radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.x.ra {-radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.x.rb {-radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.x.xo {-radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.x.rc {-radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.m {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.xfx {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.inst.xl {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.predicted_taken {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.valid {-height 18 -radix hexadecimal} /Program_test/uut/frontend/fst_stream_d.trans_cmplt {-height 18 -radix hexadecimal}} /Program_test/uut/frontend/fst_stream_d
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/seq_ctr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/hold_stream
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/schedule_stall
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/predec
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/predec_d
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_ready
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/issue_slots_i
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/ready
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
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fubm_io/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fubm_io/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fubm_io/ready
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fubm_io/stall
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fubm_io/issue
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fubm_io/predec
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fubm_io/del_commit
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fubm_io/ack
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/fubm_io/next_ack
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/inst
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/resbus
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/ir
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/aa
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bb
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/cc
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/en
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/next_en
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/addr
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/wdata
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/req
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/next_req
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/we
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/next_we
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/except_align
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/res_valid
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/res
add wave -noupdate -radix hexadecimal /Program_test/uut/opbus/opbus_0
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/addr_width
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/data_width
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/byteen
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/num_bytes
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/Clk
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/MAddr
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/MCmd
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/MData
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/MDataValid
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/MRespAccept
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/SData
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/SDataAccept
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/SResp
add wave -noupdate -radix hexadecimal /Program_test/iobus_if/MByteEn
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_io/DEST_SIZE
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_io/delayed
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_io/wb_req
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_io/wb_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_io/wb_dest_valid
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_io/wb_ack
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_io/scheduled_wb
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_io/track_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_io/track_valid
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/QUEUE_DEPTH
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/STALL_ON_FULL_LATENCY
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/num_bytes
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/en
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/gpr_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/mode
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/exts
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/baddr
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/wdata
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/req
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/we
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/result
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/result_valid
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/except_alignment
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/eff_en
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/requesting
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/unaligned
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/addr
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/in
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/in_mask
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/in_sh
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/out
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/out_mask
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/out_sh
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/out_exts
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_push
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_pop
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_req_in
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_req_out
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_empty
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_almost_full
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_full
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_ret_pop
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_ret_in
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_ret_out
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_ret_empty
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_ret_almost_full
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/q_ret_full
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/resp
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/resp_data
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/resp_accept
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/wb_req
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/next_wb_req
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/delay_q_full
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/delay_wb
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/delay_always
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_fub_io/fub_io/bus_access/gpr_dest_d
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/cr
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/ctr
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/lnk
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/xer
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/xer_padding
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/msr
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/esr
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/srr0
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/srr1
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/csrr0
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/csrr1
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/mcsrr0
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/mcsrr1
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/dear
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/iccr
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/gout
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/goe
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/gin
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/cr_sel
add wave -noupdate -radix hexadecimal /Program_test/uut/write_back/cr_multi_field
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file/gpr
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file/intf_ra_sel
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file/intf_rb_sel
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file/intf_rc_sel
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file/intf_ra
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file/intf_rb
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file/intf_rc
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file_if/wa_sel
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file_if/wa_wr
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file_if/wa
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file_if/wb_sel
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file_if/wb_wr
add wave -noupdate -radix hexadecimal /Program_test/uut/gpr_file_if/wb
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/delayed
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/wb_req
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/wb_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/wb_dest_valid
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/wb_ack
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/scheduled_wb
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/track_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/track_valid
add wave -noupdate /Program_test/uut/wbc_gpr/dest
add wave -noupdate /Program_test/uut/wbc_gpr/src
add wave -noupdate /Program_test/uut/wbc_gpr/we
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/sleep
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/wakeup
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/doorbell
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/doorbell_ack
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/ext_input
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/ext_input_ack
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/other_ack
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/msr_ee
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/iccr
add wave -noupdate -radix hexadecimal -childformat {{/Program_test/pu_ctrl/mon_inst.i -radix hexadecimal} {/Program_test/pu_ctrl/mon_inst.b -radix hexadecimal} {/Program_test/pu_ctrl/mon_inst.d -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {d -radix hexadecimal}}} {/Program_test/pu_ctrl/mon_inst.xo -radix hexadecimal} {/Program_test/pu_ctrl/mon_inst.x -radix hexadecimal} {/Program_test/pu_ctrl/mon_inst.m -radix hexadecimal} {/Program_test/pu_ctrl/mon_inst.xfx -radix hexadecimal} {/Program_test/pu_ctrl/mon_inst.xl -radix hexadecimal}} -expand -subitemconfig {/Program_test/pu_ctrl/mon_inst.i {-height 18 -radix hexadecimal} /Program_test/pu_ctrl/mon_inst.b {-height 18 -radix hexadecimal} /Program_test/pu_ctrl/mon_inst.d {-height 18 -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {d -radix hexadecimal}} -expand} /Program_test/pu_ctrl/mon_inst.d.opcd {-radix hexadecimal} /Program_test/pu_ctrl/mon_inst.d.rt {-radix hexadecimal} /Program_test/pu_ctrl/mon_inst.d.ra {-radix hexadecimal} /Program_test/pu_ctrl/mon_inst.d.d {-radix hexadecimal} /Program_test/pu_ctrl/mon_inst.xo {-height 18 -radix hexadecimal} /Program_test/pu_ctrl/mon_inst.x {-height 18 -radix hexadecimal} /Program_test/pu_ctrl/mon_inst.m {-height 18 -radix hexadecimal} /Program_test/pu_ctrl/mon_inst.xfx {-height 18 -radix hexadecimal} /Program_test/pu_ctrl/mon_inst.xl {-height 18 -radix hexadecimal}} /Program_test/pu_ctrl/mon_inst
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/mon_pc
add wave -noupdate -radix hexadecimal /Program_test/pu_ctrl/mon_hold_dc
add wave -noupdate -radix hexadecimal /Program_test/uut/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/reset
add wave -noupdate -radix hexadecimal -childformat {{{/Program_test/uut/gpr_file/gpr[0]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[1]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[2]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[3]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[4]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[5]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[6]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[7]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[8]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[9]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[10]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[11]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[12]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[13]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[14]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[15]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[16]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[17]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[18]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[19]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[20]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[21]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[22]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[23]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[24]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[25]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[26]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[27]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[28]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[29]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[30]} -radix hexadecimal} {{/Program_test/uut/gpr_file/gpr[31]} -radix hexadecimal}} -expand -subitemconfig {{/Program_test/uut/gpr_file/gpr[0]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[1]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[2]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[3]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[4]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[5]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[6]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[7]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[8]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[9]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[10]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[11]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[12]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[13]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[14]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[15]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[16]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[17]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[18]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[19]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[20]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[21]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[22]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[23]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[24]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[25]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[26]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[27]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[28]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[29]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[30]} {-height 19 -radix hexadecimal} {/Program_test/uut/gpr_file/gpr[31]} {-height 19 -radix hexadecimal}} /Program_test/uut/gpr_file/gpr
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/addr_width
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/data_width
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/byteen
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/num_bytes
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/Clk
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/MAddr
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/MCmd
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/MData
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/MDataValid
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/MRespAccept
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/SData
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/SDataAccept
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/SResp
add wave -noupdate -radix hexadecimal /Program_test/dmem_bus_if/MByteEn
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/inst
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/resbus
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/ir
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/aa
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bb
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/cc
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/en
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/next_en
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/exts
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/addr
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/wdata
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/req
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/next_req
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/we
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/next_we
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/except_align
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/res_valid
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/res
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/pc_d
add wave -noupdate -radix hexadecimal /Program_test/uut/opbus/opbus_0
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/DEST_SIZE
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/delayed
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/wb_req
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/wb_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/wb_dest_valid
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/wb_ack
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/scheduled_wb
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/track_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/dwb_ls/track_valid
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/QUEUE_DEPTH
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/STALL_ON_FULL_LATENCY
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/num_bytes
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/en
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/gpr_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/mode
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/exts
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/baddr
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/wdata
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/req
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/we
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/result
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/result_valid
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/except_alignment
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/eff_en
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/requesting
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/unaligned
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/addr
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/in
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/in_mask
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/in_sh
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/out
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/out_mask
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/out_sh
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/out_exts
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_push
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_pop
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_req_in
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_req_out
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_empty
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_almost_full
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_full
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_pop
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_in
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_out
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_empty
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_almost_full
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_full
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/resp
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/resp_data
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/resp_accept
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/wb_req
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/next_wb_req
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/addr_acked
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/delay_q_full
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/delay_wb
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/delay_always
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/gpr_dest_d
add wave -noupdate -radix hexadecimal /Program_test/uut/gen_dmem_bus/fub_ls/bus_access/gpr_dest_addr_d
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/shreg_stages
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/shreg_stages_short
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/clk
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/reset
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/fst
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/predec
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/disable_wb
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ready
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/pipe_empty
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/issue
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/del_commit
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/shift
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ra
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/rb
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/rt
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ready_gpr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ready_cr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ready_ctr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ready_lnk
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ready_xer
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ready_spr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ready_msr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/empty_gpr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/empty_cr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/empty_ctr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/empty_lnk
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/empty_xer
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/empty_spr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/empty_branch
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/empty_mem
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/empty_msr
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/found_ls_gpr_delayed_w
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ready_ls_gpr_delayed_r
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/schedule_wb
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/gpr_write
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/gpr_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/gpr_read
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/gpr_read_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ready_crf
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/empty_crf
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/wb_crf_we
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/wb_crf_src
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ctr_read
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/ctr_read_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/lnk_read
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/lnk_read_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/xer_read
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/xer_read_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/branch_read
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/branch_read_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/spr_read
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/spr_read_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/mem_read
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/mem_read_dest
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/msr_read
add wave -noupdate -radix hexadecimal /Program_test/uut/frontend/inst_track/msr_read_dest
add wave -noupdate -divider {Inst_track stuff}
add wave -noupdate /Program_test/uut/frontend/wbc_gpr_p0/dest
add wave -noupdate /Program_test/uut/frontend/wbc_gpr_p0/src
add wave -noupdate /Program_test/uut/frontend/wbc_gpr_p0/we
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/DEST_SIZE
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/NUM_TESTPORTS
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/SHREG_STAGES
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/WRITE_THROUGH
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/USE_LOOKUP_CACHE
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/NUM_SHR_TESTPORTS
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/SHR_DETECT_WAW
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/SHR_STAGE_TEST_LOW
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/SHR_STAGE_PREOUT
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/LC_NUM_CLEAR_PORTS
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/clk
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/reset
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/write
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/schedule_wb
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/read_dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/read
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/predec
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/issue
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/shift
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/disable_wb
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/ready
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/empty
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/delayed_commit
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/delayed_dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/src
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/occupied
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/lc_waw_hazard
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/shr_waw_hazard
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/test
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/found
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/index
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/not_ready
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/out_dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/out_src_bits
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/out_src
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/out_valid
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/stage
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/should_insert
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/we
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/shr_empty
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/lc_empty
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/preout_dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/preout_valid
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/NUM_STAGES
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/NUM_TESTPORTS
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/DETECT_WAW
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/STAGE_TEST_LOW
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/STAGE_PREOUT
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/clk
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/reset
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/shift
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/src
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/stage
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/we
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/occupied
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/waw_hazard
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/test
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/found
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/index
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/empty
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/preout_dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/preout_src
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/preout_valid
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/out_dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/out_src
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/out_valid
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/res_shiftreg/shreg
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/DEST_SIZE
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/NUM_TESTPORTS
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/SHREG_STAGES
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/WRITE_THROUGH
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/USE_LOOKUP_CACHE
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/NUM_SHR_TESTPORTS
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/SHR_DETECT_WAW
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/SHR_STAGE_TEST_LOW
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/SHR_STAGE_PREOUT
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/LC_NUM_CLEAR_PORTS
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/clk
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/reset
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/write
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/schedule_wb
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/read_dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/read
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/predec
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/issue
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/shift
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/disable_wb
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/ready
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/empty
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/delayed_commit
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/delayed_dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/src
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/occupied
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/lc_waw_hazard
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/shr_waw_hazard
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/test
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/found
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/index
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/not_ready
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/out_dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/out_src_bits
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/out_src
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/out_valid
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/stage
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/should_insert
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/we
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/shr_empty
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/lc_empty
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/preout_dest
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/preout_valid
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/gen_lookup_cache/lc_found
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/gen_lookup_cache/lc_found_and_read
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/gen_lookup_cache/lc_clear
add wave -noupdate /Program_test/uut/frontend/inst_track/track_gpr/gen_lookup_cache/lc_clear_dest
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 2} {24065000 ps} 1} {{Cursor 3} {302170 ps} 0}
configure wave -namecolwidth 265
configure wave -valuecolwidth 137
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
WaveRestoreZoom {228230 ps} {400460 ps}
