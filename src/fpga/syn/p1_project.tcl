#implementation: "ml505"
impl -add ml505 -type fpga

#
#implementation attributes

hdl_define -set SYNTOOL_SYNPLIFY=1 SYNTHESIS=1

set_option -vlog_std sysv
set_option -num_startend_points 5
set_option -project_relative_includes 1
set_option -enable_nfilter 0
set_option -include_path ../.. 

set_option -constraint -enable pins_1.sdc

#xilinx_par attributes
set_option -job xilinx_par -add par
set_option -job xilinx_par -option enable_run 1
set_option -job xilinx_par -option run_backannotation 0
set_option -job xilinx_par -option xtclsh_option_file ise_par_script.tcl

#device options
set_option -technology Virtex5
set_option -part XC5VLX110T
set_option -package FF1136
set_option -speed_grade -1
set_option -part_companion ""

#compilation/mapping options
set_option -use_fsm_explorer 0
set_option -top_module "Fpga_top"

# mapper_options
set_option -frequency auto
set_option -write_verilog 0
set_option -write_vhdl 0

# Xilinx Virtex2
set_option -run_prop_extract 1
set_option -maxfan 10000
set_option -disable_io_insertion 0
set_option -pipe 1
set_option -update_models_cp 0
set_option -retiming 1
set_option -no_sequential_opt 0
set_option -fixgatedclocks 3
set_option -fixgeneratedclocks 3

# Xilinx Virtex5
set_option -enable_prepacking 1

# NFilter
set_option -popfeed 0
set_option -constprop 0
set_option -createhierarchy 0

# sequential_optimization_options
set_option -symbolic_fsm_compiler 1

# Compiler Options
set_option -compiler_compatible 0
set_option -resource_sharing 1
set_option -dw_foundation 1

# Xilinx
set_option -fc_phys_opt 0

#VIF options
set_option -write_vif 1

#automatic place and route (vendor) options
set_option -write_apr_constraint 1

#set result format/file last
project -result_file "./ml505/fpga_top.edf"

#design plan options
set_option -nfilter_user_path ""

#implementation: "flyspi-board"
impl -add flyspi-board -type fpga

#
#implementation attributes

set_option -vlog_std sysv
set_option -num_startend_points 5
set_option -project_relative_includes 1
set_option -hdl_define -set SYNTOOL_SYNPLIFY=1=SYNTHESIS=1
set_option -include_path {../..}

#xilinx_par attributes
set_option -job xilinx_par -add par
set_option -job xilinx_par -option enable_run 1
set_option -job xilinx_par -option run_backannotation 0

#device options
set_option -technology Spartan6
set_option -part XC6SLX150T
set_option -package CSG484
set_option -speed_grade -3
set_option -part_companion ""

#compilation/mapping options
set_option -use_fsm_explorer 0
set_option -top_module "Emsys_top"

# mapper_options
set_option -frequency auto
set_option -write_verilog 0
set_option -write_vhdl 0

# Xilinx Spartan3
set_option -run_prop_extract 1
set_option -maxfan 10000
set_option -disable_io_insertion 0
set_option -pipe 0
set_option -retiming 0
set_option -update_models_cp 0
set_option -fixgatedclocks 3
set_option -fixgeneratedclocks 3
set_option -no_sequential_opt 0

# Xilinx Spartan6
set_option -enable_prepacking 1

# NFilter
set_option -popfeed 0
set_option -constprop 0
set_option -createhierarchy 0

# Xilinx
set_option -fc_phys_opt 0

# sequential_optimization_options
set_option -symbolic_fsm_compiler 1

# Compiler Options
set_option -compiler_compatible 0
set_option -resource_sharing 1
set_option -dw_foundation 1

#VIF options
set_option -write_vif 1

#automatic place and route (vendor) options
set_option -write_apr_constraint 1

#set result format/file last
project -result_file "./flyspi-board/emsys_top.edf"

#design plan options
set_option -nfilter_user_path ""

impl -active "ml505"
