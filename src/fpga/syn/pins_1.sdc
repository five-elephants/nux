# Synopsys, Inc. constraint file
# /fastnbig/home/sfriedma/s2pp/fpga/syn/pins_1.sdc
# Written on Mon Dec 12 12:55:00 2011
# by Synplify Premier with Design Planner, E-2011.03-SP1 Scope Editor

#
# Collections
#

#
# Clocks
#
define_clock   {clk} -name {clk}  -freq 100 -clockgroup default_clkgroup_0
define_clock -disable   {n:jtag_ctrl_scan.intf\.tck_write} -name {jtag_clk_ctrl_scan}  -freq 10 -clockgroup default_clkgroup_5
define_clock -disable   {n:jtag_dmem_scan.intf\.tck_write} -name {n:jtag_dmem_scan.intf\.tck_write}  -freq 10 -clockgroup default_clkgroup_1
define_clock -disable   {n:jtag_imem_scan.intf\.tck_write} -name {n:jtag_imem_scan.intf\.tck_write}  -freq 10 -clockgroup default_clkgroup_2
define_clock   {n:jtag_scan.intf\.tck_write} -name {n:jtag_scan.intf\.tck_write}  -freq 10 -clockgroup default_clkgroup_3

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
define_attribute {p:clk} {syn_loc} {AH15}
define_attribute {p:resetb} {syn_loc} {E9}
define_attribute {p:status_led} {syn_loc} {F6}
define_attribute {p:gpled[3]} {syn_loc} {AD26}
define_attribute {p:gpled[2]} {syn_loc} {G15}
define_attribute {p:gpled[1]} {syn_loc} {L18}
define_attribute {p:gpled[0]} {syn_loc} {H18}
define_attribute -disable {p:jtag_led[2]} {syn_loc} {AD24}
define_attribute -disable {p:jtag_led[1]} {syn_loc} {AD25}
define_attribute -disable {p:jtag_led[0]} {syn_loc} {G16}
define_attribute {p:heartbeat} {syn_loc} {AE24}
define_attribute {p:sleep} {syn_loc} {T10}

#
# I/O Standards
#
define_io_standard -disable      -default_input -delay_type input
define_io_standard -disable      -default_output -delay_type output
define_io_standard -disable      -default_bidir -delay_type bidir
define_io_standard               {clk} -delay_type input syn_pad_type {LVCMOS_33}
define_io_standard               {reset} -delay_type input syn_pad_type {LVCMOS_33}
define_io_standard               {status_led} -delay_type output syn_pad_type {LVCMOS_25}
define_io_standard               {gpled[3:0]} -delay_type output syn_pad_type {LVCMOS_25}
define_io_standard -disable      {jtag_led[2:0]} syn_pad_type {LVCMOS_25}
define_io_standard               {sleep} syn_pad_type {LVCMOS_25}
define_io_standard               {heartbeat} syn_pad_type {LVCMOS_25}

#
# Compile Points
#

#
# Other
#
