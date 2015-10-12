onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider Masters
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_a/MByteEn
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_b/MByteEn
add wave -noupdate /Bus_test/master_arb/resetb
add wave -noupdate /Bus_test/master_arb/empty
add wave -noupdate /Bus_test/master_arb/full
add wave -noupdate /Bus_test/master_arb/push
add wave -noupdate /Bus_test/master_arb/pop
add wave -noupdate /Bus_test/master_arb/resp_sel_in
add wave -noupdate /Bus_test/master_arb/resp_sel_out
add wave -noupdate /Bus_test/master_arb/req_state
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_c/MByteEn
add wave -noupdate /Bus_test/master_arb_bc/resetb
add wave -noupdate /Bus_test/master_arb_bc/empty
add wave -noupdate /Bus_test/master_arb_bc/full
add wave -noupdate /Bus_test/master_arb_bc/push
add wave -noupdate /Bus_test/master_arb_bc/pop
add wave -noupdate /Bus_test/master_arb_bc/resp_sel_in
add wave -noupdate /Bus_test/master_arb_bc/resp_sel_out
add wave -noupdate /Bus_test/master_arb_bc/req_state
add wave -noupdate -divider Slaves
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_0/MByteEn
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_1/MByteEn
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_2/MByteEn
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_slave_3/MByteEn
add wave -noupdate -divider {Bus tree}
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_master/MByteEn
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_master_d/MByteEn
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_0_if/MByteEn
add wave -noupdate /Bus_test/bus_split_0/push
add wave -noupdate /Bus_test/bus_split_0/pop
add wave -noupdate /Bus_test/bus_split_0/full
add wave -noupdate /Bus_test/bus_split_0/empty
add wave -noupdate /Bus_test/bus_split_0/resp_sel_in
add wave -noupdate /Bus_test/bus_split_0/resp_sel_out
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/Clk
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/MReset_n
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/MAddr
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/MCmd
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/MData
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/MDataValid
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/MRespAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/SCmdAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/SData
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/SDataAccept
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/SResp
add wave -noupdate -radix hexadecimal /Bus_test/bus_split_1_if/MByteEn
add wave -noupdate -divider Cache
add wave -noupdate -radix hexadecimal /Bus_test/cache_read_if/en
add wave -noupdate -radix hexadecimal /Bus_test/cache_read_if/addr
add wave -noupdate -radix hexadecimal /Bus_test/cache_read_if/data_r
add wave -noupdate -radix hexadecimal /Bus_test/cache_read_if/data_w
add wave -noupdate -radix hexadecimal /Bus_test/cache_read_if/we
add wave -noupdate -radix hexadecimal /Bus_test/cache_read_if/be
add wave -noupdate -radix hexadecimal /Bus_test/cache_read_if/delay
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/clk
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/reset
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/state
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/valids
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/tags
add wave -noupdate -radix hexadecimal -expand -subitemconfig {/Bus_test/read_cache/addr.tag {-height 17 -radix hexadecimal} /Bus_test/read_cache/addr.index {-height 17 -radix hexadecimal} /Bus_test/read_cache/addr.displ {-height 17 -radix hexadecimal}} /Bus_test/read_cache/addr
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/addr_d
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/fetch_addr
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/miss
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/tag
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/valid
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/tag_w
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/valid_w
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/we
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/valid_mask
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/valid_mask_a
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/valid_mask_b
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/start_line_fetch
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/requesting
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/responding
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/inc_req_cnt
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/set_req_cnt
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/inc_resp_cnt
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/set_resp_cnt
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/new_req_cnt
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/req_cnt
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/new_resp_cnt
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/resp_cnt
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/stop_cnt
add wave -noupdate -radix hexadecimal /Bus_test/read_cache/en_d
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_r/en
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_r/addr
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_r/data_r
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_r/data_w
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_r/we
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_r/be
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_r/delay
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_w/en
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_w/addr
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_w/data_r
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_w/data_w
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_w/we
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_w/be
add wave -noupdate -radix hexadecimal /Bus_test/cache_store_w/delay
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {396908606 ps} 0}
configure wave -namecolwidth 219
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
WaveRestoreZoom {396685047 ps} {397205932 ps}
