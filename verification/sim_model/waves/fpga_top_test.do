onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/clk
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/resetb
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/status_led
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/gpled
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/sleep
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/heartbeat
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_hold
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/core_reset
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_gout
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_gin
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/ctrl_reg
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/sysclk
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/sysrst
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/sleep
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/wakeup
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/doorbell
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/doorbell_ack
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/ext_input
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/ext_input_ack
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/other_ack
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/msr_ee
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/iccr
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/mon_inst
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/mon_pc
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pu_ctrl/mon_hold_dc
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/imem_if/en
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/imem_if/addr
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/imem_if/data_r
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/imem_if/data_w
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/imem_if/we
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/imem_if/be
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/imem_if/delay
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/dmem_if/en
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/dmem_if/addr
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/dmem_if/data_r
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/dmem_if/data_w
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/dmem_if/we
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/dmem_if/be
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/dmem_if/delay
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/clk
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/reset
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/hold
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/gout
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/gin
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/goe
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend_control
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/branch_control
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/interrupt_control
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/opf_predec
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/opf_issue
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/issue
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/res
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/opbus_i
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/predicted_taken
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/clk
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/reset
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/ctrl
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/bctrl
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/ictrl
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/opf_predec
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/opf_issue
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/issue_slots
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/predicted_taken
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/sleeping
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/mon_inst
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/mon_pc
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/fst_d
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/fst_stream
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/fst_stream_d
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/seq_ctr
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/hold_stream
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/schedule_stall
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/predec
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/predec_d
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/inst_ready
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/issue_slots_i
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/ready
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/issue
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/mc_hold
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/pipe_empty_track
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/pipe_empty
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/ignore_inst
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/csync
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/int_csync
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/disable_wb
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/jumping
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/jumping_d
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/eff_bctrl
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/div_stall
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/ls_stall
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/frontend/stalled_by_fubs
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/gpr_file/gpr
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/clk
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/reset
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/cr
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/ctr
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/lnk
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/xer
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/xer_padding
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/msr
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/esr
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/srr0
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/srr1
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/csrr0
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/csrr1
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/mcsrr0
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/mcsrr1
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/dear
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/iccr
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/gout
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/goe
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/gin
add wave -noupdate -radix hexadecimal /Fpga_top_test/uut/pcore/write_back/cr_sel
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {25408480000 ps} 1} {{Cursor 2} {25408560402 ps} 0}
configure wave -namecolwidth 223
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
WaveRestoreZoom {25408466385 ps} {25408897869 ps}
