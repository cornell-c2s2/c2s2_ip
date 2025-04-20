# Copyright (C) 2024  Intel Corporation. All rights reserved.
# Your use of Intel Corporation's design tools, logic functions 
# and other software and tools, and any partner logic 
# functions, and any output files from any of the foregoing 
# (including device programming or simulation files), and any 
# associated documentation or information are expressly subject 
# to the terms and conditions of the Intel Program License 
# Subscription Agreement, the Intel Quartus Prime License Agreement,
# the Intel FPGA IP License Agreement, or other applicable license
# agreement, including, without limitation, that your use is for
# the sole purpose of programming logic devices manufactured by
# Intel and sold by Intel or its authorized distributors.  Please
# refer to the applicable agreement for further details, at
# https://fpgasoftware.intel.com/eula.

# Quartus Prime: Generate Tcl File for Project
# File: emulation_sp24_tapein2.tcl
# Generated on: Wed Dec 11 00:05:06 2024

# Load Quartus Prime Tcl Project package
package require ::quartus::project
load_package flow

set need_to_close_project 0
set make_assignments 1

# Check that the right project is open
if {[is_project_open]} {
	if {[string compare $quartus(project) "emulation_sp24_tapein2"]} {
		puts "Project emulation_sp24_tapein2 is not open"
		set make_assignments 0
	}
} else {
	# Only open if not already open
	if {[project_exists emulation_sp24_tapein2]} {
		project_open -revision emulation_sp24_tapein2 emulation_sp24_tapein2
	} else {
		project_new -revision emulation_sp24_tapein2 emulation_sp24_tapein2
	}
	set need_to_close_project 1
}

# Make assignments
if {$make_assignments} {
	set_global_assignment -name FAMILY "Cyclone IV E"
	set_global_assignment -name DEVICE EP4CE115F29C7
	set_global_assignment -name TOP_LEVEL_ENTITY tapein1_sp25_top
	set_global_assignment -name VERILOG_FILE interconnect_fpga.v
	set_global_assignment -name SDC_FILE timing.sdc
  set_global_assignment -name PROJECT_OUTPUT_DIRECTORY output_files
	set_global_assignment -name ORIGINAL_QUARTUS_VERSION 18.1.0
	set_global_assignment -name PROJECT_CREATION_TIME_DATE "17:28:04  DECEMBER 05, 2024"
	set_global_assignment -name LAST_QUARTUS_VERSION "23.1std.1 Lite Edition"
	set_global_assignment -name PARTITION_NETLIST_TYPE SOURCE -section_id Top
	set_global_assignment -name PARTITION_FITTER_PRESERVATION_LEVEL PLACEMENT_AND_ROUTING -section_id Top
	set_global_assignment -name PARTITION_COLOR 16764057 -section_id Top
	set_global_assignment -name MIN_CORE_JUNCTION_TEMP 0
	set_global_assignment -name MAX_CORE_JUNCTION_TEMP 85
	set_global_assignment -name POWER_PRESET_COOLING_SOLUTION "23 MM HEAT SINK WITH 200 LFPM AIRFLOW"
	set_global_assignment -name POWER_BOARD_THERMAL_MODEL "NONE (CONSERVATIVE)"
	set_global_assignment -name VERILOG_INPUT_VERSION SYSTEMVERILOG_2005
	set_global_assignment -name VERILOG_SHOW_LMF_MAPPING_MESSAGES OFF
	set_location_assignment PIN_Y2 -to CLOCK_50
	set_location_assignment PIN_AB22 -to GPIO0
	set_location_assignment PIN_AB21 -to GPIO2
	set_location_assignment PIN_AC21 -to GPIO4
	set_location_assignment PIN_AD21 -to GPIO6
	set_location_assignment PIN_AC15 -to GPIO1
	set_location_assignment PIN_G19 -to LEDR0
	set_location_assignment PIN_F19 -to LEDR1
	set_instance_assignment -name PARTITION_HIERARCHY root_partition -to | -section_id Top

	# Commit assignments
	export_assignments

	# Compile the design
	execute_flow -compile

	if {$need_to_close_project} {
		project_close
	}
}