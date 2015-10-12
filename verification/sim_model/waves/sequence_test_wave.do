onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal /Sequence_test/uut/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/hold
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gout
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gin
add wave -noupdate -radix hexadecimal /Sequence_test/uut/goe
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend_control
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/branch_control.jump -radix hexadecimal} {/Sequence_test/uut/branch_control.jump_vec -radix hexadecimal} {/Sequence_test/uut/branch_control.fb_taken -radix hexadecimal} {/Sequence_test/uut/branch_control.fb_not_taken -radix hexadecimal} {/Sequence_test/uut/branch_control.fb_pc -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/branch_control.jump {-height 18 -radix hexadecimal} /Sequence_test/uut/branch_control.jump_vec {-height 18 -radix hexadecimal} /Sequence_test/uut/branch_control.fb_taken {-height 18 -radix hexadecimal} /Sequence_test/uut/branch_control.fb_not_taken {-height 18 -radix hexadecimal} /Sequence_test/uut/branch_control.fb_pc {-height 18 -radix hexadecimal}} /Sequence_test/uut/branch_control
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/interrupt_control.jump -radix hexadecimal} {/Sequence_test/uut/interrupt_control.jump_vec -radix hexadecimal} {/Sequence_test/uut/interrupt_control.fb_taken -radix hexadecimal} {/Sequence_test/uut/interrupt_control.fb_not_taken -radix hexadecimal} {/Sequence_test/uut/interrupt_control.fb_pc -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/interrupt_control.jump {-height 18 -radix hexadecimal} /Sequence_test/uut/interrupt_control.jump_vec {-height 18 -radix hexadecimal} /Sequence_test/uut/interrupt_control.fb_taken {-height 18 -radix hexadecimal} /Sequence_test/uut/interrupt_control.fb_not_taken {-height 18 -radix hexadecimal} /Sequence_test/uut/interrupt_control.fb_pc {-height 18 -radix hexadecimal}} /Sequence_test/uut/interrupt_control
add wave -noupdate -radix hexadecimal /Sequence_test/uut/opf_predec
add wave -noupdate -radix hexadecimal /Sequence_test/uut/opf_issue
add wave -noupdate -radix hexadecimal /Sequence_test/uut/issue
add wave -noupdate -radix hexadecimal /Sequence_test/uut/res
add wave -noupdate -radix hexadecimal /Sequence_test/uut/opbus_i
add wave -noupdate -radix hexadecimal /Sequence_test/uut/predicted_taken
add wave -noupdate -divider Interfaces
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/sleep
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/wakeup
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/doorbell
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/doorbell_ack
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/ext_input
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/ext_input_ack
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/other_ack
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/msr_ee
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/iccr
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/mon_inst
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/mon_pc
add wave -noupdate -radix hexadecimal /Sequence_test/pu_ctrl_if/mon_hold_dc
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_if/en
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_if/addr
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_if/data_r
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_if/data_w
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_if/we
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_if/be
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_if/delay
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/Clk
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/MReset_n
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/MAddr
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/MCmd
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/MData
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/MDataValid
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/MRespAccept
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/SData
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/SDataAccept
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/SResp
add wave -noupdate -radix hexadecimal /Sequence_test/dmem_bus_if/MByteEn
add wave -noupdate -radix hexadecimal /Sequence_test/imem_if/en
add wave -noupdate -radix hexadecimal /Sequence_test/imem_if/addr
add wave -noupdate -radix hexadecimal /Sequence_test/imem_if/data_r
add wave -noupdate -radix hexadecimal /Sequence_test/imem_if/data_w
add wave -noupdate -radix hexadecimal /Sequence_test/imem_if/we
add wave -noupdate -radix hexadecimal /Sequence_test/imem_if/be
add wave -noupdate -radix hexadecimal /Sequence_test/imem_if/delay
add wave -noupdate -radix hexadecimal /Sequence_test/iobus_if/Clk
add wave -noupdate -radix hexadecimal /Sequence_test/iobus_if/MAddr
add wave -noupdate -radix hexadecimal /Sequence_test/iobus_if/MCmd
add wave -noupdate -radix hexadecimal /Sequence_test/iobus_if/MData
add wave -noupdate -radix hexadecimal /Sequence_test/iobus_if/MDataValid
add wave -noupdate -radix hexadecimal /Sequence_test/iobus_if/MRespAccept
add wave -noupdate -radix hexadecimal /Sequence_test/iobus_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Sequence_test/iobus_if/SData
add wave -noupdate -radix hexadecimal /Sequence_test/iobus_if/SDataAccept
add wave -noupdate -radix hexadecimal /Sequence_test/iobus_if/SResp
add wave -noupdate -divider Frontend
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/ctrl
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/bctrl
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/ictrl
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/opf_predec
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/opf_issue
add wave -noupdate -radix hexadecimal -childformat {{{/Sequence_test/uut/frontend/issue_slots[0]} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[1]} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2]} -radix hexadecimal -childformat {{{/Sequence_test/uut/frontend/issue_slots[2].ir} -radix hexadecimal -childformat {{{/Sequence_test/uut/frontend/issue_slots[2].ir.i} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.b} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.d} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.xo} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.x} -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {{/Sequence_test/uut/frontend/issue_slots[2].ir.m} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.xfx} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.xl} -radix hexadecimal}}} {{/Sequence_test/uut/frontend/issue_slots[2].pc} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].npc} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].valid} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].thread} -radix hexadecimal}}} {{/Sequence_test/uut/frontend/issue_slots[3]} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[4]} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[5]} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[6]} -radix hexadecimal}} -subitemconfig {{/Sequence_test/uut/frontend/issue_slots[0]} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[1]} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2]} {-height 17 -radix hexadecimal -childformat {{{/Sequence_test/uut/frontend/issue_slots[2].ir} -radix hexadecimal -childformat {{{/Sequence_test/uut/frontend/issue_slots[2].ir.i} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.b} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.d} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.xo} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.x} -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {{/Sequence_test/uut/frontend/issue_slots[2].ir.m} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.xfx} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.xl} -radix hexadecimal}}} {{/Sequence_test/uut/frontend/issue_slots[2].pc} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].npc} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].valid} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].thread} -radix hexadecimal}} -expand} {/Sequence_test/uut/frontend/issue_slots[2].ir} {-height 17 -radix hexadecimal -childformat {{{/Sequence_test/uut/frontend/issue_slots[2].ir.i} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.b} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.d} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.xo} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.x} -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {{/Sequence_test/uut/frontend/issue_slots[2].ir.m} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.xfx} -radix hexadecimal} {{/Sequence_test/uut/frontend/issue_slots[2].ir.xl} -radix hexadecimal}} -expand} {/Sequence_test/uut/frontend/issue_slots[2].ir.i} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.b} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.d} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.xo} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.x} {-height 17 -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}} -expand} {/Sequence_test/uut/frontend/issue_slots[2].ir.x.opcd} {-radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.x.rt} {-radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.x.ra} {-radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.x.rb} {-radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.x.xo} {-radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.x.rc} {-radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.m} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.xfx} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].ir.xl} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].pc} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].npc} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].valid} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[2].thread} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[3]} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[4]} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[5]} {-height 17 -radix hexadecimal} {/Sequence_test/uut/frontend/issue_slots[6]} {-radix hexadecimal}} /Sequence_test/uut/frontend/issue_slots
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/predicted_taken
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/sleeping
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/frontend/fst_d.pc -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.npc -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.inst -radix hexadecimal -childformat {{/Sequence_test/uut/frontend/fst_d.inst.i -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.inst.b -radix hexadecimal -childformat {{opcd -radix hexadecimal} {bo -radix hexadecimal} {bi -radix hexadecimal} {bd -radix hexadecimal} {aa -radix hexadecimal} {lk -radix hexadecimal}}} {/Sequence_test/uut/frontend/fst_d.inst.d -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.inst.xo -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {oe -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {/Sequence_test/uut/frontend/fst_d.inst.x -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {/Sequence_test/uut/frontend/fst_d.inst.m -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.inst.xfx -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.inst.xl -radix hexadecimal}}} {/Sequence_test/uut/frontend/fst_d.predicted_taken -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.valid -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.trans_cmplt -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/frontend/fst_d.pc {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/fst_d.npc {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst {-height 18 -radix hexadecimal -childformat {{/Sequence_test/uut/frontend/fst_d.inst.i -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.inst.b -radix hexadecimal -childformat {{opcd -radix hexadecimal} {bo -radix hexadecimal} {bi -radix hexadecimal} {bd -radix hexadecimal} {aa -radix hexadecimal} {lk -radix hexadecimal}}} {/Sequence_test/uut/frontend/fst_d.inst.d -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.inst.xo -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {oe -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {/Sequence_test/uut/frontend/fst_d.inst.x -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {/Sequence_test/uut/frontend/fst_d.inst.m -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.inst.xfx -radix hexadecimal} {/Sequence_test/uut/frontend/fst_d.inst.xl -radix hexadecimal}} -expand} /Sequence_test/uut/frontend/fst_d.inst.i {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.b {-height 18 -radix hexadecimal -childformat {{opcd -radix hexadecimal} {bo -radix hexadecimal} {bi -radix hexadecimal} {bd -radix hexadecimal} {aa -radix hexadecimal} {lk -radix hexadecimal}}} /Sequence_test/uut/frontend/fst_d.inst.b.opcd {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.b.bo {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.b.bi {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.b.bd {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.b.aa {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.b.lk {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.d {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.xo {-height 18 -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {oe -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} /Sequence_test/uut/frontend/fst_d.inst.xo.opcd {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.xo.rt {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.xo.ra {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.xo.rb {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.xo.oe {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.xo.xo {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.xo.rc {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.x {-height 18 -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}} -expand} /Sequence_test/uut/frontend/fst_d.inst.x.opcd {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.x.rt {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.x.ra {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.x.rb {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.x.xo {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.x.rc {-radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.m {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.xfx {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/fst_d.inst.xl {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/fst_d.predicted_taken {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/fst_d.valid {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/fst_d.trans_cmplt {-height 18 -radix hexadecimal}} /Sequence_test/uut/frontend/fst_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fst_stream
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fst_stream_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/seq_ctr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/hold_stream
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/schedule_stall
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/predec
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/schedule/state
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/frontend/predec_d.read_ra -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_rb -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_rt -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.write_ra -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.write_rt -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.ra -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.rb -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.rt -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.b_immediate -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_ctr -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.write_ctr -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_lnk -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.write_lnk -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.write_cr -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_cr_0 -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_cr_1 -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_cr_2 -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_xer -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.write_xer -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.xer_dest -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_spr -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_spr2 -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.spr -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.spr2 -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.write_spr -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.spr_dest -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.write_mem -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.read_msr -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.write_msr -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.fu_set -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.context_sync -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.mem_bar -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.halt -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.nd_latency -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.latency -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.multicycles -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.is_multicycle -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.is_branch -radix hexadecimal} {/Sequence_test/uut/frontend/predec_d.is_nop -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/frontend/predec_d.read_ra {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_rb {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_rt {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.write_ra {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.write_rt {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.ra {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.rb {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.rt {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.b_immediate {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_ctr {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.write_ctr {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_lnk {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.write_lnk {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.write_cr {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_cr_0 {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_cr_1 {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_cr_2 {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_xer {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.write_xer {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.xer_dest {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_spr {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_spr2 {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.spr {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.spr2 {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.write_spr {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.spr_dest {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.write_mem {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.read_msr {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.write_msr {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.fu_set {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.context_sync {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.mem_bar {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.halt {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.nd_latency {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.latency {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.multicycles {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.is_multicycle {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.is_branch {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/predec_d.is_nop {-height 17 -radix hexadecimal}} /Sequence_test/uut/frontend/predec_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/issue_slots_i
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/issue
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/mc_hold
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/pipe_empty
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/ignore_inst
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/csync
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/int_csync
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/disable_wb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/jumping
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/frontend/eff_bctrl.jump -radix hexadecimal} {/Sequence_test/uut/frontend/eff_bctrl.jump_vec -radix hexadecimal} {/Sequence_test/uut/frontend/eff_bctrl.fb_taken -radix hexadecimal} {/Sequence_test/uut/frontend/eff_bctrl.fb_not_taken -radix hexadecimal} {/Sequence_test/uut/frontend/eff_bctrl.fb_pc -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/frontend/eff_bctrl.jump {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/eff_bctrl.jump_vec {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/eff_bctrl.fb_taken {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/eff_bctrl.fb_not_taken {-height 18 -radix hexadecimal} /Sequence_test/uut/frontend/eff_bctrl.fb_pc {-height 18 -radix hexadecimal}} /Sequence_test/uut/frontend/eff_bctrl
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/div_stall
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/ls_stall
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/stalled_by_fubs
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/cr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/ctr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/lnk
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/write_back/xer.so -radix hexadecimal} {/Sequence_test/uut/write_back/xer.ov -radix hexadecimal} {/Sequence_test/uut/write_back/xer.ca -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/write_back/xer.so {-height 18 -radix hexadecimal} /Sequence_test/uut/write_back/xer.ov {-height 18 -radix hexadecimal} /Sequence_test/uut/write_back/xer.ca {-height 18 -radix hexadecimal}} /Sequence_test/uut/write_back/xer
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/msr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/esr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/srr0
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/srr1
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/csrr0
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/csrr1
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/mcsrr0
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/mcsrr1
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/dear
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/iccr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/gout
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/goe
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/gin
add wave -noupdate -radix hexadecimal /Sequence_test/uut/write_back/cr_sel
add wave -noupdate -radix hexadecimal -childformat {{{/Sequence_test/uut/gpr_file/gpr[0]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[1]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[2]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[3]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[4]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[5]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[6]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[7]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[8]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[9]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[10]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[11]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[12]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[13]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[14]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[15]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[16]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[17]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[18]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[19]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[20]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[21]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[22]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[23]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[24]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[25]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[26]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[27]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[28]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[29]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[30]} -radix hexadecimal} {{/Sequence_test/uut/gpr_file/gpr[31]} -radix hexadecimal}} -expand -subitemconfig {{/Sequence_test/uut/gpr_file/gpr[0]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[1]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[2]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[3]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[4]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[5]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[6]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[7]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[8]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[9]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[10]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[11]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[12]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[13]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[14]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[15]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[16]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[17]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[18]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[19]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[20]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[21]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[22]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[23]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[24]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[25]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[26]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[27]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[28]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[29]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[30]} {-height 18 -radix hexadecimal} {/Sequence_test/uut/gpr_file/gpr[31]} {-height 18 -radix hexadecimal}} /Sequence_test/uut/gpr_file/gpr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/wbc_gpr/dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/wbc_gpr/src
add wave -noupdate -radix hexadecimal /Sequence_test/uut/wbc_gpr/we
add wave -noupdate -radix unsigned /Sequence_test/uut/frontend/wbc_gpr_p0/dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/wbc_gpr_p0/src
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/wbc_gpr_p0/we
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/wbc_gpr_p1/dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/wbc_gpr_p1/src
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/wbc_gpr_p1/we
add wave -noupdate -radix hexadecimal /Sequence_test/uut/dwb_ls/delayed
add wave -noupdate -radix hexadecimal /Sequence_test/uut/dwb_ls/wb_req
add wave -noupdate -radix hexadecimal /Sequence_test/uut/dwb_ls/wb_dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/dwb_ls/wb_ack
add wave -noupdate -radix hexadecimal /Sequence_test/uut/resbus/res_0
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/resbus/res_1.res_a -radix hexadecimal} {/Sequence_test/uut/resbus/res_1.res_b -radix hexadecimal} {/Sequence_test/uut/resbus/res_1.cout -radix hexadecimal} {/Sequence_test/uut/resbus/res_1.ov -radix hexadecimal} {/Sequence_test/uut/resbus/res_1.crf -radix hexadecimal} {/Sequence_test/uut/resbus/res_1.msr -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/resbus/res_1.res_a {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_1.res_b {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_1.cout {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_1.ov {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_1.crf {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_1.msr {-height 18 -radix hexadecimal}} /Sequence_test/uut/resbus/res_1
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/resbus/res_2.res_a -radix hexadecimal} {/Sequence_test/uut/resbus/res_2.res_b -radix hexadecimal} {/Sequence_test/uut/resbus/res_2.cout -radix hexadecimal} {/Sequence_test/uut/resbus/res_2.ov -radix hexadecimal} {/Sequence_test/uut/resbus/res_2.crf -radix hexadecimal} {/Sequence_test/uut/resbus/res_2.msr -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/resbus/res_2.res_a {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_2.res_b {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_2.cout {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_2.ov {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_2.crf {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_2.msr {-height 18 -radix hexadecimal}} /Sequence_test/uut/resbus/res_2
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/resbus/res_3.res_a -radix hexadecimal} {/Sequence_test/uut/resbus/res_3.res_b -radix hexadecimal} {/Sequence_test/uut/resbus/res_3.cout -radix hexadecimal} {/Sequence_test/uut/resbus/res_3.ov -radix hexadecimal} {/Sequence_test/uut/resbus/res_3.crf -radix hexadecimal} {/Sequence_test/uut/resbus/res_3.msr -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/resbus/res_3.res_a {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_3.res_b {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_3.cout {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_3.ov {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_3.crf {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_3.msr {-height 18 -radix hexadecimal}} /Sequence_test/uut/resbus/res_3
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/resbus/res_4.res_a -radix hexadecimal} {/Sequence_test/uut/resbus/res_4.res_b -radix hexadecimal} {/Sequence_test/uut/resbus/res_4.cout -radix hexadecimal} {/Sequence_test/uut/resbus/res_4.ov -radix hexadecimal} {/Sequence_test/uut/resbus/res_4.crf -radix hexadecimal} {/Sequence_test/uut/resbus/res_4.msr -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/resbus/res_4.res_a {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_4.res_b {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_4.cout {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_4.ov {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_4.crf {-height 18 -radix hexadecimal} /Sequence_test/uut/resbus/res_4.msr {-height 18 -radix hexadecimal}} /Sequence_test/uut/resbus/res_4
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/fub_fxdpt/opbus/opbus_0.a -radix hexadecimal} {/Sequence_test/uut/fub_fxdpt/opbus/opbus_0.b -radix hexadecimal} {/Sequence_test/uut/fub_fxdpt/opbus/opbus_0.c -radix hexadecimal} {/Sequence_test/uut/fub_fxdpt/opbus/opbus_0.cin -radix hexadecimal} {/Sequence_test/uut/fub_fxdpt/opbus/opbus_0.so -radix hexadecimal} {/Sequence_test/uut/fub_fxdpt/opbus/opbus_0.cr -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/fub_fxdpt/opbus/opbus_0.a {-height 18 -radix hexadecimal} /Sequence_test/uut/fub_fxdpt/opbus/opbus_0.b {-height 18 -radix hexadecimal} /Sequence_test/uut/fub_fxdpt/opbus/opbus_0.c {-height 18 -radix hexadecimal} /Sequence_test/uut/fub_fxdpt/opbus/opbus_0.cin {-height 18 -radix hexadecimal} /Sequence_test/uut/fub_fxdpt/opbus/opbus_0.so {-height 18 -radix hexadecimal} /Sequence_test/uut/fub_fxdpt/opbus/opbus_0.cr {-height 18 -radix hexadecimal}} /Sequence_test/uut/fub_fxdpt/opbus/opbus_0
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/DEST_SIZE
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/NUM_TESTPORTS
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/SHREG_STAGES
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/write
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/read_dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/read
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/predec
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/issue
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/shift
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/disable_wb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/empty
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/src
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/occupied
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/test
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/found
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/index
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/not_ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/out_dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/out_src_bits
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/out_src
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/out_valid
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/stage
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/should_insert
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/DEST_SIZE
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/SRC_SIZE
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/NUM_STAGES
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/NUM_TESTPORTS
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/DETECT_WAW
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/shift
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/src
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/stage
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/we
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/occupied
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/waw_hazard
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/test
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/found
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/index
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/empty
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/out_dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/out_src
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/out_valid
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/res_shiftreg/shreg
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/so
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/result
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/alu_res
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/alu_cout
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/alu_crf
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/rotm_res
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/rotm_cout
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/rotm_crf
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/spreu_res
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/mul_res_hi
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/mul_res_lo
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/mul_crf_hi
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/mul_crf_lo
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/div_res
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/div_crf
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/res
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/cout
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/crf
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/spreu_sprout
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/fixedpoint/spreu_msrout
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/inst
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/alu_op
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/cr_op
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/fxdp_sel
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/alu_crl_ba
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/alu_crl_bb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/alu_crl_bt
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/src_cr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/reg_mv
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/ir
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/decode/oe
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/en_int
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/alu_op
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/cr_op
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/crl_ba
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/crl_bb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/crl_bt
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/reg_mv
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/src_cr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/mul_unsigned
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/mul_high
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/div_unsigned
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/sel
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/sel_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/mul_high_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/mul_en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/mul_ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/mul_complete
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/div_en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/div_ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/div_complete
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/oe
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/oe_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/fub_fxdpt/ctrl/oe_shreg
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/inst
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/resbus
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/ir
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/thread_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/mul_en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/next_mul_en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/mul_high
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/mul_high_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/so_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/oe_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/mul_unsigned
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/next_mul_high
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/next_mul_unsigned
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/next_div_unsigned
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/mul_res_hi
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/mul_res_lo
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/mul_crf_hi
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/mul_crf_lo
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/aa
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/bb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_mul/fub_mul/so
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/mcheck_mcheck
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/critical_cinput
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/critical_cdoorbell
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/base_ext_input
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/base_ext_input_ack
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/base_alignment
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/base_illegal
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/base_trap
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/base_unimplemented
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/base_doorbell
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/base_doorbell_ack
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/other_ack
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/pc
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/pc_alignment
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/pc_trap
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_base
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_base_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_base_d2
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_base_wb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_crit
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_crit_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_crit_d2
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_crit_wb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_mcheck
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_mcheck_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_mcheck_d2
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/rest_mcheck_wb
add wave -noupdate -divider Divider
add wave -noupdate -radix hexadecimal /Sequence_test/uut/int_sched_if/block_external
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/stall
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/issue
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/predec
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/on_state
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/ctr_ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/wb_ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/gpr_dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/cr_dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/xer_dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/oe
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/ctr/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/ctr/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/ctr/ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/ctr/issue
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/ctr/ctr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/fubm_div/ctr/next_ctr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/inst
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/resbus
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/ir
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/thread_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div_en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/next_div_en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div_unsigned
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/next_div_unsigned
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div_ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div_complete
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div_res
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div_crf
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/aa
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/bb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/oe_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/so
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/so_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/STAGES
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/uns
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/a
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/b
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/ready
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/complete
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/quotient
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/remainder
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/div_by_zero
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/crf
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/a_ext
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/b_ext
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/s_start
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/u_start
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/s_complete
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/u_complete
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/s_div_by_zero
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/u_div_by_zero
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/s_quotient
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/u_quotient
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/u_quot_ext
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/s_remainder
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/u_remainder
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/u_rem_ext
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/next_quotient
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/next_remainder
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/a_sgn
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/b_sgn
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/illegal_signed_ops
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/uns_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/state
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/next_crf
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_fub_div/fub_div/div/next_div_by_zero
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/frontend/inst_track/del_commit.valid -radix hexadecimal} {/Sequence_test/uut/frontend/inst_track/del_commit.gpr -radix hexadecimal} {/Sequence_test/uut/frontend/inst_track/del_commit.mem -radix hexadecimal} {/Sequence_test/uut/frontend/inst_track/del_commit.io -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/frontend/inst_track/del_commit.valid {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/inst_track/del_commit.gpr {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/inst_track/del_commit.mem {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/inst_track/del_commit.io {-height 17 -radix hexadecimal}} /Sequence_test/uut/frontend/inst_track/del_commit
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/schedule_wb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/out_dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/out_src_bits
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/out_src
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_track/track_gpr/out_valid
add wave -noupdate -divider {New Divider}
add wave -noupdate -radix hexadecimal /Sequence_test/uut/opbus/opbus_0
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/gpr_dest
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/mode
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/exts
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/baddr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/wdata
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/req
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/we
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/result
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/result_valid
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/except_alignment
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/pipe_empty
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/eff_en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/requesting
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/unaligned
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/addr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/in
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/in_mask
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/in_sh
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/out
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/out_mask
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/out_sh
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/out_exts
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_push
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_pop
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_req_in
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_req_out
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_empty
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_almost_full
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_full
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_pop
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_in
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_out
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_empty
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_almost_full
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/q_ret_full
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/resp
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/resp_data
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/resp_accept
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/wb_req
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/next_wb_req
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/addr_acked
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/delay_q_full
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/delay_wb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/delay_always
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/gpr_dest_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_access/gpr_dest_addr_d
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/en
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/en_dec
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/en_int
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/dis_ex
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/en_dec_d
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/we
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/ls_we
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/multiple
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/ls_multiple
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/first_cycle
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/ls_first_cycle
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/multiple_inc
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/ls_multiple_inc
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/mode
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/ls_mode
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/return_dout
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/exts
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/is_update_op
add wave -noupdate /Sequence_test/uut/gen_dmem_bus/fub_ls/ctrl/do_request
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/inst
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/predec
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/resbus
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/pipe_empty
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/gen_dmem_bus/fub_ls/ir.i -radix hexadecimal} {/Sequence_test/uut/gen_dmem_bus/fub_ls/ir.b -radix hexadecimal} {/Sequence_test/uut/gen_dmem_bus/fub_ls/ir.d -radix hexadecimal} {/Sequence_test/uut/gen_dmem_bus/fub_ls/ir.xo -radix hexadecimal} {/Sequence_test/uut/gen_dmem_bus/fub_ls/ir.x -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {/Sequence_test/uut/gen_dmem_bus/fub_ls/ir.m -radix hexadecimal} {/Sequence_test/uut/gen_dmem_bus/fub_ls/ir.xfx -radix hexadecimal} {/Sequence_test/uut/gen_dmem_bus/fub_ls/ir.xl -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/gen_dmem_bus/fub_ls/ir.i {-height 17 -radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.b {-height 17 -radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.d {-height 17 -radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.xo {-height 17 -radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.x {-height 17 -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}} -expand} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.x.opcd {-radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.x.rt {-radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.x.ra {-radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.x.rb {-radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.x.xo {-radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.x.rc {-radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.m {-height 17 -radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.xfx {-height 17 -radix hexadecimal} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir.xl {-height 17 -radix hexadecimal}} /Sequence_test/uut/gen_dmem_bus/fub_ls/ir
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/aa
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bb
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/cc
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/next_en
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/exts
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/addr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/addr_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/wb_addr_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/wdata
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/req
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/next_req
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/we
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/next_we
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/except_align
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/res_valid
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/res
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/pc_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/inst_valid_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/bus_queue_empty
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/rt_d
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/fub_ls/addr_cycle
add wave -noupdate -radix hexadecimal /Sequence_test/uut/clk
add wave -noupdate -radix hexadecimal /Sequence_test/uut/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/hold
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gout
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gin
add wave -noupdate -radix hexadecimal /Sequence_test/uut/goe
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend_control
add wave -noupdate -radix hexadecimal /Sequence_test/uut/branch_control
add wave -noupdate -radix hexadecimal /Sequence_test/uut/interrupt_control
add wave -noupdate -radix hexadecimal /Sequence_test/uut/opf_predec
add wave -noupdate -radix hexadecimal /Sequence_test/uut/issue_predec
add wave -noupdate -radix hexadecimal /Sequence_test/uut/opf_issue
add wave -noupdate -radix hexadecimal /Sequence_test/uut/issue
add wave -noupdate -radix hexadecimal /Sequence_test/uut/res
add wave -noupdate -radix hexadecimal /Sequence_test/uut/opbus_i
add wave -noupdate -radix hexadecimal /Sequence_test/uut/predicted_taken
add wave -noupdate -radix hexadecimal /Sequence_test/uut/io_pipe_empty
add wave -noupdate -radix hexadecimal /Sequence_test/uut/ls_pipe_empty
add wave -noupdate -radix hexadecimal /Sequence_test/uut/issue__FUB_ID_FIXEDPOINT
add wave -noupdate -radix hexadecimal /Sequence_test/uut/res__FUB_ID_FIXEDPOINT
add wave -noupdate -radix hexadecimal /Sequence_test/uut/issue__FUB_ID_BRANCH
add wave -noupdate -radix hexadecimal /Sequence_test/uut/res__FUB_ID_BRANCH
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/issue__FUB_ID_LOAD_STORE
add wave -noupdate -radix hexadecimal /Sequence_test/uut/gen_dmem_bus/res__FUB_ID_LOAD_STORE
add wave -noupdate -radix hexadecimal /Sequence_test/prog/rprog
add wave -noupdate /Sequence_test/uut/frontend/inst_stream/clk
add wave -noupdate /Sequence_test/uut/frontend/inst_stream/reset
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/hold
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/bctrl
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/fst
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/iaddr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/next_iaddr
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/iaddr_inc
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/iaddr_d
add wave -noupdate -radix hexadecimal -childformat {{/Sequence_test/uut/frontend/inst_stream/data_r.i -radix hexadecimal} {/Sequence_test/uut/frontend/inst_stream/data_r.b -radix hexadecimal} {/Sequence_test/uut/frontend/inst_stream/data_r.d -radix hexadecimal} {/Sequence_test/uut/frontend/inst_stream/data_r.xo -radix hexadecimal} {/Sequence_test/uut/frontend/inst_stream/data_r.x -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}}} {/Sequence_test/uut/frontend/inst_stream/data_r.m -radix hexadecimal} {/Sequence_test/uut/frontend/inst_stream/data_r.xfx -radix hexadecimal} {/Sequence_test/uut/frontend/inst_stream/data_r.xl -radix hexadecimal}} -expand -subitemconfig {/Sequence_test/uut/frontend/inst_stream/data_r.i {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.b {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.d {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.xo {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.x {-height 17 -radix hexadecimal -childformat {{opcd -radix hexadecimal} {rt -radix hexadecimal} {ra -radix hexadecimal} {rb -radix hexadecimal} {xo -radix hexadecimal} {rc -radix hexadecimal}} -expand} /Sequence_test/uut/frontend/inst_stream/data_r.x.opcd {-radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.x.rt {-radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.x.ra {-radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.x.rb {-radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.x.xo {-radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.x.rc {-radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.m {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.xfx {-height 17 -radix hexadecimal} /Sequence_test/uut/frontend/inst_stream/data_r.xl {-height 17 -radix hexadecimal}} /Sequence_test/uut/frontend/inst_stream/data_r
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/p_taken
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/p_target
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/en_shift
add wave -noupdate -radix hexadecimal /Sequence_test/uut/frontend/inst_stream/delay_d
add wave -noupdate -divider {FUB NEVER}
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/clk
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/reset
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/inst
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/resbus
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/lut
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/ir
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/aa
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/bb
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/cc
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/map_res
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/select_res
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/lut_sel
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/next_select_state
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/select_state
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/next_save_select_state
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/save_select_state
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/next_output_map
add wave -noupdate /Sequence_test/uut/gen_fub_never/fub_never/output_map
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {15718306 ps} 0} {{Cursor 2} {5692980625 ps} 1}
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
WaveRestoreZoom {15668227 ps} {15774398 ps}
