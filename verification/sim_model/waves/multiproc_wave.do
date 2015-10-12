onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal /Multiproc_test/clk
add wave -noupdate -radix hexadecimal /Multiproc_test/resetb
add wave -noupdate /Multiproc_test/uut/elem_resets
add wave -noupdate -radix hexadecimal /Multiproc_test/status_led
add wave -noupdate -radix hexadecimal /Multiproc_test/gpled
add wave -noupdate -radix hexadecimal /Multiproc_test/sleep
add wave -noupdate -radix hexadecimal /Multiproc_test/mon_pc
add wave -noupdate -radix hexadecimal /Multiproc_test/heartbeat
add wave -noupdate -radix hexadecimal /Multiproc_test/jtag/tdi
add wave -noupdate -radix hexadecimal /Multiproc_test/jtag/tdo
add wave -noupdate -radix hexadecimal /Multiproc_test/jtag/tck
add wave -noupdate -radix hexadecimal /Multiproc_test/jtag/tms
add wave -noupdate -radix hexadecimal /Multiproc_test/jtag/tdi_sl
add wave -noupdate -radix hexadecimal /Multiproc_test/jtag/tms_sl
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/clk
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/resetb
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/status_led
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/gpled
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/sleep
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/heartbeat
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/sysclk
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/sysrst
add wave -noupdate -divider {Element 0}
add wave -noupdate -radix hexadecimal -expand -subitemconfig {/Multiproc_test/uut/el_0/pcore/frontend/fst_d.pc {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.npc {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst {-height 18 -radix hexadecimal -expand} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.i {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.b {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.d {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.xo {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.x {-height 18 -radix hexadecimal -expand} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.x.opcd {-radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.x.rt {-radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.x.ra {-radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.x.rb {-radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.x.xo {-radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.x.rc {-radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.m {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.xfx {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.inst.xl {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.predicted_taken {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.valid {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_0/pcore/frontend/fst_d.trans_cmplt {-height 18 -radix hexadecimal}} /Multiproc_test/uut/el_0/pcore/frontend/fst_d
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_0/pcore/frontend/predec_d
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_0/pcore/frontend/bctrl
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_0/pcore/frontend/ictrl
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_0/pcore/frontend/issue_slots
add wave -noupdate -divider {Element 1}
add wave -noupdate -radix hexadecimal -expand -subitemconfig {/Multiproc_test/uut/el_1/pcore/frontend/fst_d.pc {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.npc {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst {-height 18 -radix hexadecimal -expand} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.i {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.b {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.d {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.xo {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.x {-height 18 -radix hexadecimal -expand} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.x.opcd {-radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.x.rt {-radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.x.ra {-radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.x.rb {-radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.x.xo {-radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.x.rc {-radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.m {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.xfx {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.inst.xl {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.predicted_taken {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.valid {-height 18 -radix hexadecimal} /Multiproc_test/uut/el_1/pcore/frontend/fst_d.trans_cmplt {-height 18 -radix hexadecimal}} /Multiproc_test/uut/el_1/pcore/frontend/fst_d
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_1/pcore/frontend/predec_d
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_1/pcore/frontend/bctrl
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_1/pcore/frontend/ictrl
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_1/pcore/frontend/issue_slots
add wave -noupdate -divider {Element 2}
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_2/pcore/frontend/fst_d
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_2/pcore/frontend/predec_d
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_2/pcore/frontend/bctrl
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_2/pcore/frontend/ictrl
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/el_2/pcore/frontend/issue_slots
add wave -noupdate -divider {Message queue}
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_01/push
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_01/pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_01/fifo_full
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_01/fifo_empty
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_01/fifo_din
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_01/fifo_dout
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_02/push
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_02/next_pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_02/pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_02/fifo_full
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_02/fifo_empty
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_02/fifo_din
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_02/fifo_dout
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_10/push
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_10/next_pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_10/pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_10/fifo_full
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_10/fifo_empty
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_10/fifo_din
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_10/fifo_dout
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_12/push
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_12/next_pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_12/pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_12/fifo_full
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_12/fifo_empty
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_12/fifo_din
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_12/fifo_dout
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_20/push
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_20/next_pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_20/pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_20/fifo_full
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_20/fifo_empty
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_20/fifo_din
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_20/fifo_dout
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_21/push
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_21/next_pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_21/pop
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_21/fifo_full
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_21/fifo_empty
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_21/fifo_din
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/q_21/fifo_dout
add wave -noupdate -divider Programming
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_if/en
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_if/addr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_if/data_r
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_if/data_w
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_if/we
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_if/be
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_if/delay
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_sysctrl/en
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_sysctrl/addr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_sysctrl/data_r
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_sysctrl/data_w
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_sysctrl/we
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_sysctrl/be
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_sysctrl/delay
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_elems/en
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_elems/addr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_elems/data_r
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_elems/data_w
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_elems/we
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_elems/be
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_elems/delay
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_0_if/en
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_0_if/addr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_0_if/data_r
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_0_if/data_w
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_0_if/we
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_0_if/be
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_0_if/delay
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_1_if/en
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_1_if/addr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_1_if/data_r
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_1_if/data_w
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_1_if/we
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_1_if/be
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/prog_el_1_if/delay
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/Clk
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/MReset_n
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/MAddr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/MCmd
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/MData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/MDataValid
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/MRespAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/SCmdAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/SData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/SDataAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/SResp
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_to_0_out/MByteEn
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/Clk
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/MReset_n
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/MAddr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/MCmd
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/MData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/MDataValid
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/MRespAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/SCmdAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/SData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/SDataAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/SResp
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_out/MByteEn
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/Clk
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/MReset_n
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/MAddr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/MCmd
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/MData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/MDataValid
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/MRespAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/SCmdAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/SData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/SDataAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/SResp
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1/MByteEn
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/Clk
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MReset_n
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MAddr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MCmd
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MDataValid
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MRespAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/SCmdAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/SData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/SDataAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/SResp
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MByteEn
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/Clk
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/MReset_n
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/MAddr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/MCmd
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/MData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/MDataValid
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/MRespAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/SCmdAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/SData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/SDataAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/SResp
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_1_in/MByteEn
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/Clk
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MReset_n
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MAddr
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MCmd
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MDataValid
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MRespAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/SCmdAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/SData
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/SDataAccept
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/SResp
add wave -noupdate -radix hexadecimal /Multiproc_test/uut/io_0_to_1_in/MByteEn
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {60825000 ps} 0}
configure wave -namecolwidth 232
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
WaveRestoreZoom {0 ps} {105 us}
