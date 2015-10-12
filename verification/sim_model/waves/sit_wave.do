onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -subitemconfig {/Sit_mod/uut/decode_data/inst.xo -expand /Sit_mod/uut/decode_data/inst.xo.rt {-radix unsigned} /Sit_mod/uut/decode_data/inst.xo.ra {-radix unsigned} /Sit_mod/uut/decode_data/inst.xo.rb {-radix unsigned}} /Sit_mod/uut/decode_data/inst
add wave -noupdate -radix hexadecimal /Sit_mod/uut/decode_data/pc
add wave -noupdate -radix hexadecimal /Sit_mod/uut/decode_data/npc
add wave -noupdate -radix decimal /Sit_mod/uut/gpr_file/gpr
add wave -noupdate /Sit_mod/uut/reg_file/cr
add wave -noupdate /Sit_mod/uut/reg_file/xer
add wave -noupdate /Sit_mod/uut/reg_file/ctr
add wave -noupdate /Sit_mod/uut/reg_file/lnk
add wave -noupdate /Sit_mod/uut/reg_file/gout_reg
add wave -noupdate /Sit_mod/uut/reg_file/csrr0
add wave -noupdate /Sit_mod/uut/reg_file/csrr1
add wave -noupdate /Sit_mod/uut/reg_file/dear
add wave -noupdate /Sit_mod/uut/reg_file/esr
add wave -noupdate -radix hexadecimal /Sit_mod/uut/reg_file/mcsrr0
add wave -noupdate -radix hexadecimal /Sit_mod/uut/reg_file/mcsrr1
add wave -noupdate /Sit_mod/uut/reg_file/msr
add wave -noupdate /Sit_mod/uut/reg_file/srr0
add wave -noupdate /Sit_mod/uut/reg_file/srr1
add wave -noupdate -divider Fixedpoint
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/clk
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/reset
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/alu_op
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/cr_op
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/crl_ba
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/crl_bb
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/crl_bt
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/reg_mv
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/src_cr
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/mul_unsigned
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/mul_high
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/sel
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/sel_d
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/mul_high_d
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/mul_en
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/mul_ready
add wave -noupdate /Sit_mod/uut/fixedpoint_ctrl/mul_complete
add wave -noupdate /Sit_mod/uut/fixedpoint_data/alu_a_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/alu_a_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/alu_b_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/alu_b_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/alu_cin
add wave -noupdate /Sit_mod/uut/fixedpoint_data/alu_cr_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/alu_cr_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/rotm_x_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/rotm_x_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/rotm_q_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/rotm_q_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/rotm_sh
add wave -noupdate /Sit_mod/uut/fixedpoint_data/rotm_ma
add wave -noupdate /Sit_mod/uut/fixedpoint_data/rotm_mb
add wave -noupdate /Sit_mod/uut/fixedpoint_data/spreu_cr_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/spreu_cr_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/spreu_a_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/spreu_a_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/spreu_sprin
add wave -noupdate /Sit_mod/uut/fixedpoint_data/spreu_msrin
add wave -noupdate /Sit_mod/uut/fixedpoint_data/mul_a_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/mul_a_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/mul_b_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/mul_b_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/div_a_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/div_a_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/div_b_in
add wave -noupdate /Sit_mod/uut/fixedpoint_data/div_b_out
add wave -noupdate /Sit_mod/uut/fixedpoint_data/res
add wave -noupdate /Sit_mod/uut/fixedpoint/alu_res
add wave -noupdate /Sit_mod/uut/fixedpoint/alu_cout
add wave -noupdate /Sit_mod/uut/fixedpoint/alu_crf
add wave -noupdate /Sit_mod/uut/fixedpoint/rotm_res
add wave -noupdate /Sit_mod/uut/fixedpoint/rotm_cout
add wave -noupdate /Sit_mod/uut/fixedpoint/rotm_crf
add wave -noupdate /Sit_mod/uut/fixedpoint/spreu_res
add wave -noupdate /Sit_mod/uut/fixedpoint/spreu_crf
add wave -noupdate /Sit_mod/uut/fixedpoint/mul_res_hi
add wave -noupdate /Sit_mod/uut/fixedpoint/mul_res_lo
add wave -noupdate /Sit_mod/uut/fixedpoint/mul_crf_hi
add wave -noupdate /Sit_mod/uut/fixedpoint/mul_crf_lo
add wave -noupdate /Sit_mod/uut/fixedpoint/div_res
add wave -noupdate /Sit_mod/uut/fixedpoint/div_crf
add wave -noupdate /Sit_mod/uut/fixedpoint/res
add wave -noupdate /Sit_mod/uut/fixedpoint/cout
add wave -noupdate /Sit_mod/uut/fixedpoint/crf
add wave -noupdate /Sit_mod/uut/fixedpoint/spreu_sprout
add wave -noupdate /Sit_mod/uut/fixedpoint/spreu_msrout
add wave -noupdate /Sit_mod/uut/fixedpoint/gen_mul/mul/s_prod
add wave -noupdate /Sit_mod/uut/fixedpoint/gen_mul/mul/s_complete
add wave -noupdate /Sit_mod/uut/fixedpoint/gen_mul/mul/u_prod
add wave -noupdate /Sit_mod/uut/fixedpoint/gen_mul/mul/u_complete
add wave -noupdate /Sit_mod/uut/fixedpoint/gen_div/div/s_complete
add wave -noupdate /Sit_mod/uut/fixedpoint/gen_div/div/u_complete
add wave -noupdate /Sit_mod/uut/fixedpoint/gen_div/div/s_div_by_zero
add wave -noupdate /Sit_mod/uut/fixedpoint/gen_div/div/u_div_by_zero
add wave -noupdate -radix hexadecimal /Sit_mod/uut/fixedpoint/gen_div/div/s_quotient
add wave -noupdate -radix hexadecimal /Sit_mod/uut/fixedpoint/gen_div/div/u_quotient
add wave -noupdate -radix hexadecimal /Sit_mod/uut/fixedpoint/gen_div/div/s_remainder
add wave -noupdate -radix hexadecimal /Sit_mod/uut/fixedpoint/gen_div/div/u_remainder
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 2} {121658541 ps} 0}
configure wave -namecolwidth 291
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
WaveRestoreZoom {121472649 ps} {122295683 ps}
