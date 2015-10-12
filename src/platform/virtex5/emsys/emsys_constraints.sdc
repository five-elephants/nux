# Synopsys, Inc. constraint file
# /superfast/home/sfriedma/s2pp/fpga/syn/emsys_constraints.sdc
# Written on Wed Apr 10 15:45:56 2013
# by Synplify Premier with Design Planner, F-2012.03 Scope Editor

#
# Collections
#

#
# Clocks
#
define_clock   {clk_in} -name {clk}  -freq 100 -clockgroup default_clkgroup_0
define_clock -disable   {n:jtag_ctrl_scan.intf\.tck_write} -name {jtag_clk_ctrl_scan}  -freq 10 -clockgroup default_clkgroup_5
define_clock -disable   {n:jtag_dmem_scan.intf\.tck_write} -name {n:jtag_dmem_scan.intf\.tck_write}  -freq 10 -clockgroup default_clkgroup_1
define_clock -disable   {n:jtag_imem_scan.intf\.tck_write} -name {n:jtag_imem_scan.intf\.tck_write}  -freq 10 -clockgroup default_clkgroup_2
define_clock -disable   {n:jtag_scan.intf\.tck_write} -name {n:jtag_scan.intf\.tck_write}  -freq 10 -clockgroup default_clkgroup_3
define_clock   {n:jtag_in.jtag.intf\.tck_write} -name {JTAG_clk}  -freq 10 -clockgroup default_clkgroup_4

#
# Clock to Clock
#

#
# Inputs/Outputs
#
define_input_delay -disable      -default -improve 0.00 -route 0.00
define_output_delay -disable     -default -improve 0.00 -route 0.00
define_input_delay -disable      {clk} -improve 0.00 -route 0.00
define_input_delay -disable      {reset} -improve 0.00 -route 0.00
define_output_delay -disable     {status_led} -improve 0.00 -route 0.00
define_output_delay -disable     {gpled[3:0]} -improve 0.00 -route 0.00
define_input_delay -disable      {} -improve 0.00 -route 0.00

#
# Registers
#

#
# Delay Paths
#

#
# Attributes
#
define_attribute {p:clk_in} {syn_loc} {AH15}
define_attribute {p:resetb} {syn_loc} {E9}
define_attribute {p:status_led} {syn_loc} {F6}
define_attribute {p:gpled[3]} {syn_loc} {AD26}
define_attribute {p:gpled[2]} {syn_loc} {G15}
define_attribute {p:gpled[1]} {syn_loc} {L18}
define_attribute {p:gpled[0]} {syn_loc} {H18}
define_attribute {p:heartbeat} {syn_loc} {AE24}
define_attribute {p:sleep} {syn_loc} {T10}
define_attribute {p:sl_tdo} {syn_loc} {AA34}
define_attribute {p:sl_tdi} {syn_loc} {AD32}
define_attribute {p:sl_tms} {syn_loc} {P34}
define_attribute {p:sl_tck} {syn_loc} {N34}
define_attribute {p:sl_gpio[3]} {syn_loc} {F34}
define_attribute {p:sl_gpio[2]} {syn_loc} {H34}
define_attribute {p:sl_gpio[1]} {syn_loc} {G33}
define_attribute {p:sl_gpio[0]} {syn_loc} {G32}
define_attribute {p:gen_clk} {syn_loc} {H32}
define_attribute {p:feten} {syn_loc} {H33}

#
# I/O Standards
#
define_io_standard               -default_input -delay_type input
define_io_standard               -default_output -delay_type output
define_io_standard               -default_bidir -delay_type bidir
define_io_standard               {clk_in} -delay_type input syn_pad_type {LVCMOS_33}
define_io_standard               {reset} -delay_type input syn_pad_type {LVCMOS_33}
define_io_standard               {status_led} -delay_type output syn_pad_type {LVCMOS_25}
define_io_standard               {gpled[3:0]} -delay_type output syn_pad_type {LVCMOS_25}
define_io_standard               {jtag_led[2:0]} syn_pad_type {LVCMOS_25}
define_io_standard               {sleep} syn_pad_type {LVCMOS_25}
define_io_standard               {heartbeat} syn_pad_type {LVCMOS_25}
define_io_standard               {sl_tdo} syn_pad_type {LVCMOS_25}
define_io_standard               {sl_tdi} syn_pad_type {LVCMOS_25}
define_io_standard               {sl_tms} syn_pad_type {LVCMOS_25}
define_io_standard               {sl_tck} syn_pad_type {LVCMOS_25}
define_io_standard               {sl_gpio[3:0]} syn_pad_type {LVCMOS_25}
define_io_standard               {gen_clk} syn_pad_type {LVCMOS_25}
define_io_standard               {feten} syn_pad_type {LVCMOS_25}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}
define_io_standard               {}

#
# Compile Points
#

#
# Other
#
