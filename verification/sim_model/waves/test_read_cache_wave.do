onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal /Test_read_cache/clk
add wave -noupdate -radix hexadecimal /Test_read_cache/reset
add wave -noupdate -radix hexadecimal /Test_read_cache/read_bus/en
add wave -noupdate -radix hexadecimal /Test_read_cache/read_bus/addr
add wave -noupdate -radix hexadecimal /Test_read_cache/read_bus/data_r
add wave -noupdate -radix hexadecimal /Test_read_cache/read_bus/data_w
add wave -noupdate -radix hexadecimal /Test_read_cache/read_bus/we
add wave -noupdate -radix hexadecimal /Test_read_cache/read_bus/be
add wave -noupdate -radix hexadecimal /Test_read_cache/read_bus/delay
add wave -noupdate -radix hexadecimal /Test_read_cache/store_r/en
add wave -noupdate -radix hexadecimal /Test_read_cache/store_r/addr
add wave -noupdate -radix hexadecimal /Test_read_cache/store_r/data_r
add wave -noupdate -radix hexadecimal /Test_read_cache/store_r/data_w
add wave -noupdate -radix hexadecimal /Test_read_cache/store_r/we
add wave -noupdate -radix hexadecimal /Test_read_cache/store_r/be
add wave -noupdate -radix hexadecimal /Test_read_cache/store_r/delay
add wave -noupdate -radix hexadecimal /Test_read_cache/store_w/en
add wave -noupdate -radix hexadecimal /Test_read_cache/store_w/addr
add wave -noupdate -radix hexadecimal /Test_read_cache/store_w/data_r
add wave -noupdate -radix hexadecimal /Test_read_cache/store_w/data_w
add wave -noupdate -radix hexadecimal /Test_read_cache/store_w/we
add wave -noupdate -radix hexadecimal /Test_read_cache/store_w/be
add wave -noupdate -radix hexadecimal /Test_read_cache/store_w/delay
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/Clk
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/MReset_n
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/MAddr
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/MCmd
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/MData
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/MDataValid
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/MRespAccept
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/SCmdAccept
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/SData
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/SDataAccept
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/SResp
add wave -noupdate -radix hexadecimal /Test_read_cache/fetch_bus/MByteEn
add wave -noupdate -divider {Cache internals}
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/clk
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/reset
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/state
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/valids
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/tags
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/addr
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/addr_d
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/fetch_addr
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/miss
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/tag
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/valid
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/cmp_valid
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/data_w
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/tag_w
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/valid_w
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/we
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/valid_mask
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/valid_mask_a
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/valid_mask_b
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/start_line_fetch
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/requesting
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/responding
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/inc_req_cnt
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/set_req_cnt
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/inc_resp_cnt
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/set_resp_cnt
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/new_req_cnt
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/req_cnt
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/new_resp_cnt
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/resp_cnt
add wave -noupdate -radix hexadecimal /Test_read_cache/uut/stop_cnt
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {520940 ps} 0}
configure wave -namecolwidth 228
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
WaveRestoreZoom {0 ps} {189430 ps}
