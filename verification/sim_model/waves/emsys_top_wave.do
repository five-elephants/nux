onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider {Toplevel Pins}
add wave -noupdate -radix hexadecimal /Emsys_top_test/clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/resetb
add wave -noupdate -radix hexadecimal /Emsys_top_test/sl_tdo
add wave -noupdate -radix hexadecimal /Emsys_top_test/sl_tdi
add wave -noupdate -radix hexadecimal /Emsys_top_test/sl_tms
add wave -noupdate -radix hexadecimal /Emsys_top_test/sl_tck
add wave -noupdate -radix hexadecimal /Emsys_top_test/sl_gpio
add wave -noupdate -radix hexadecimal /Emsys_top_test/gen_clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/feten
add wave -noupdate -radix hexadecimal /Emsys_top_test/status_led
add wave -noupdate -radix hexadecimal /Emsys_top_test/gpled
add wave -noupdate -radix hexadecimal /Emsys_top_test/sleep
add wave -noupdate -radix hexadecimal /Emsys_top_test/heartbeat
add wave -noupdate -divider Internals
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/on_state
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/readback_en
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/readback_clear
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/readback_reg
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/jtag_if/tck
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/jtag_if/treset
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/jtag_if/tdo
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/jtag_if/tdi
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/jtag_if/sel
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/jtag_if/shift
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/jtag_if/capture
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/jtag_if/update
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/ram_if/en
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/ram_if/addr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/ram_if/data_r
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/ram_if/data_w
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/ram_if/we
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/ram_if/be
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/jtag_in/ram_if/delay
add wave -noupdate -divider {Bus Infrastructure}
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_jtag_in/MByteEn
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master/MByteEn
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_master_d/MByteEn
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/delay_master/req_state
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/delay_master/resp_state
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc/MByteEn
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_0_if/MByteEn
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_split_1_if/MByteEn
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_proc_mem/MByteEn
add wave -noupdate -divider {Memory block}
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/proc_mem/mem_if/en
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/proc_mem/mem_if/addr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/proc_mem/mem_if/data_r
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/proc_mem/mem_if/data_w
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/proc_mem/mem_if/we
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/proc_mem/mem_if/be
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/proc_mem/mem_if/delay
add wave -noupdate -divider {Instruction fetching}
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/INDEX_SIZE
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/DISPLACEMENT_SIZE
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/TAG_SIZE
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/WORD_SIZE
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/NUM_ROWS
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/NUM_WORDS
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/reset
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/state
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/valids
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/tags
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/addr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/addr_d
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/fetch_addr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/miss
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/tag
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/valid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/tag_w
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/valid_w
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/we
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/valid_mask
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/valid_mask_a
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/valid_mask_b
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/start_line_fetch
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/requesting
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/responding
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/inc_req_cnt
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/set_req_cnt
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/inc_resp_cnt
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/set_resp_cnt
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/new_req_cnt
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/req_cnt
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/new_resp_cnt
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/resp_cnt
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/inst_cache/stop_cnt
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MByteEn
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_dmem_arb/resetb
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_dmem_arb/empty
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_dmem_arb/full
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_dmem_arb/push
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_dmem_arb/pop
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_dmem_arb/resp_sel_in
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_dmem_arb/resp_sel_out
add wave -noupdate -divider {Control registers}
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/core_reset
add wave -noupdate -radix hexadecimal -expand -subitemconfig {{/Emsys_top_test/uut/cregs[0]} {-height 17 -radix hexadecimal}} /Emsys_top_test/uut/cregs
add wave -noupdate -radix hexadecimal -expand -subitemconfig {/Emsys_top_test/uut/creg_resets.dummy {-radix hexadecimal} /Emsys_top_test/uut/creg_resets.core_reset_b {-radix hexadecimal}} /Emsys_top_test/uut/creg_resets
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/cregs_target/regs
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/cregs_target/base_masked
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/cregs_target/offset_masked
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/cregs_target/regs_i
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/bus_cregs/MByteEn
add wave -noupdate -divider {Frequency synthesis}
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/clk_from_ibufg
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/clk_from_dcm
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/pll_clk_fast
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/pll_clk_slow
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/gen_clk
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm_locked
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/pll_locked
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/CLKFX
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/DRDY
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/LOCKED
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/DO
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/CLKIN
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/DCLK
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/DEN
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/DWE
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/RST
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/DI
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/dcm/DADDR
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/pll/CLKOUT0
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/pll/CLKOUT1
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/pll/LOCKED
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/pll/CLKIN
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/pll/RST
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/clk_oddr/Q
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/clk_oddr/C
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/clk_oddr/CE
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/clk_oddr/D1
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/clk_oddr/D2
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/state
add wave -noupdate -group {Frequency synthesis} /Emsys_top_test/uut/freq_synth/wr_creg
add wave -noupdate -group {Frequency synthesis} -expand /Emsys_top_test/uut/freq_synth/creg
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/Clk
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/MReset_n
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/MAddr
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/MCmd
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/MData
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/MDataValid
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/MRespAccept
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/SCmdAccept
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/SData
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/SDataAccept
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/SResp
add wave -noupdate -group {Frequency synthesis} -radix hexadecimal /Emsys_top_test/uut/bus_freq_synth/MByteEn
add wave -noupdate -divider Processor
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/sleep
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/wakeup
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/doorbell
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/doorbell_ack
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/ext_input
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/ext_input_ack
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/other_ack
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/msr_ee
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/iccr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/mon_inst
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/mon_pc
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pu_ctrl/mon_hold_dc
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/reset
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/hold
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/gout
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/gin
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/goe
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend_control
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/branch_control
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/interrupt_control
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/opf_predec
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/issue_predec
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/opf_issue
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/issue
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/res
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/opbus_i
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/predicted_taken
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/io_pipe_empty
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/ls_pipe_empty
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/issue__FUB_ID_FIXEDPOINT
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/res__FUB_ID_FIXEDPOINT
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/issue__FUB_ID_BRANCH
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/res__FUB_ID_BRANCH
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/dmem_bus_if/MByteEn
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_if/en
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_if/addr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_if/data_r
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_if/data_w
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_if/we
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_if/be
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_if/delay
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/Clk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MReset_n
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MAddr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MCmd
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MDataValid
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MRespAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/SData
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/SDataAccept
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/SResp
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/imem_bus_if/MByteEn
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/gpr_file/gpr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/cr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/ctr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/lnk
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/xer
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/xer_padding
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/msr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/esr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/srr0
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/srr1
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/csrr0
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/csrr1
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/mcsrr0
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/mcsrr1
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/dear
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/iccr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/gout
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/goe
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/gin
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/write_back/cr_sel
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/io_pipe_empty
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/ls_pipe_empty
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/ctrl
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/bctrl
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/ictrl
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/issue_slots
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/predicted_taken
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/sleeping
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/fst_d
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/seq_ctr
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/hold_stream
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/schedule_stall
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/predec_d
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/inst_ready
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/ready
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/issue
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/mc_hold
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/pipe_empty_track
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/pipe_empty
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/ignore_inst
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/csync
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/int_csync
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/disable_wb
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/jumping
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/jumping_d
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/eff_bctrl
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/div_stall
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/ls_stall
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/io_stall
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/stalled_by_fubs
add wave -noupdate -radix hexadecimal /Emsys_top_test/uut/gen_proc/pcore/frontend/about_to_halt
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {24235000 ps} 0}
configure wave -namecolwidth 215
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
WaveRestoreZoom {22699727 ps} {24994112 ps}
