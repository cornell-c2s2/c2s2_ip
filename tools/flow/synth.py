# Push a file through caravel synthesis (openlane)
from utils.invoke import caravel_dir, caravel_link, caravel_installed, run, link, cp
from utils.cmdline import SubCommand, multi_type, positive_int
import logging as log
from utils.misc import load_config, merge_dict, root_dir, build_dir, split_path
from utils.logging import Spinner
import json
import subprocess
from os import path
import os
import tempfile
import itertools
import re
import multiprocessing


# Take a list of designs and collect the design files for them
def design_files(build: str, designs: list[dict], args) -> list[dict]:
    # ----------------------------------------------------------------
    # Run pytest to generate the designs
    # ----------------------------------------------------------------
    # get only the name of the build directory
    build_name = path.basename(build)

    spinner = Spinner(args, f"Running pytest in {build} to generate verilog files")

    design_dir = path.abspath(path.dirname(args.design))
    # get the pytest files
    pytest_files = set(sum([design.get("TEST_FILES", []) for design in designs], []))
    if len(pytest_files) == 0:
        pytest_files = [design_dir]
        log.info("No pytest files specified, running pytest on %s", design_dir)
    else:
        pytest_files = [path.join(design_dir, file) for file in pytest_files]
        log.info("Running pytest on %s", pytest_files)

    subprocess.run(
        [
            "pytest",
            *pytest_files,
            "-n",
            "auto",
            "--test-verilog",
            "--dump-vtb",
            "--build-dir",
            build_name,
        ]
        + (["-v"] if args.verbose > 1 else []),
        stdout=subprocess.DEVNULL if args.verbose == 0 else None,
    )

    spinner.succeed("Finished running pytest")

    # ----------------------------------------------------------------
    # Collect the design files
    # in the format DESIGNNAME__PARAMETER_VALUE__PARAMETER2_VALUE__pickled.v
    # ----------------------------------------------------------------

    # Change the design names to be of the form
    # DESIGNNAME__PARAMETER_VALUE__PARAMETER2_VALUE (used by pymtl)

    spinner = Spinner(args, "Collecting design files")

    for design in designs:
        synth_params = [
            f"{k}_{v}" for k, v in design.get("SYNTH_PARAMETERS", {}).items()
        ]
        # get possible design names (permutations of parameters)
        top_module = design["DESIGN_NAME"]
        design["ORIGINAL_DESIGN_NAME"] = top_module
        design["DESIGN_NAME"] = set()
        if len(synth_params) == 0:
            design["DESIGN_NAME"].add(f"{top_module}_noparam")
        else:
            for params in itertools.permutations(synth_params):
                design["DESIGN_NAME"].add("__".join([top_module, *params]))

    unique_design_names = set.union(*[d["DESIGN_NAME"] for d in designs])
    log.debug("Searching for designs matching %s", unique_design_names)

    # Walk through the build directory and find the design files
    design_names_regex = "|".join(re.escape(name) for name in unique_design_names)
    verilog_file_regex = re.compile(
        f"^(?P<design_name>{design_names_regex})__pickled\\.v$"
    )
    vtb_file_regex = re.compile(
        f"^(?P<design_name>{design_names_regex}).*_tb\\.v\\.cases$"
    )
    verilog_files: dict[str, list[(str, float)]] = {}
    vtb_files: dict[str, list[str]] = {}

    for root, _, files in os.walk(build):
        for file in files:
            # Check if the file is a verilog file matching
            # DESIGNNAME__pickled.v
            match = verilog_file_regex.match(file)
            if match is not None:
                design_name = match.group("design_name")
                if design_name not in verilog_files:
                    verilog_files[design_name] = []

                verilog_files[design_name].append(
                    (path.join(root, file), path.getmtime(path.join(root, file)))
                )
            match = vtb_file_regex.match(file)
            if match is not None:
                design_name = match.group("design_name")
                if design_name not in vtb_files:
                    vtb_files[design_name] = []
                vtb_files[design_name].append(path.join(root, file))

    # Loop through the verilog files and find the most recent one
    for design_name, files in verilog_files.items():
        if len(files) > 1:
            most_recent = max(files, key=lambda x: x[1])[0]
            log.warn(
                f"Found multiple verilog files for {design_name}:\n\t%s\nUsing the last modified file %s"
                % ("\n\t".join(f[0] for f in files), most_recent)
            )
        else:
            most_recent = files[0][0]
        verilog_files[design_name] = most_recent

    log.debug("Collected verilog files %s", verilog_files)
    log.debug("Collected vtb files %s", vtb_files)

    # merge verilog and vtb files into one dict
    files: dict[str, dict[str, str]] = {}
    for design_name in verilog_files.keys():
        if design_name not in vtb_files:
            spinner.fail(f"No corresponding vtb cases found for {design_name}")
            return 1
        files[design_name] = {
            "verilog": verilog_files[design_name],
            "vtb": vtb_files.pop(design_name),
        }

    if len(vtb_files) > 0:
        log.warn(f"Found extra vtb files not matching any verilog files: {vtb_files}")

    # delete these from the scope so they don't get used later
    del verilog_files
    del vtb_files

    # match the verilog files to the designs
    for design in designs:
        design_name = None
        for name in design["DESIGN_NAME"]:
            if name in files:
                if design_name is not None:
                    spinner.fail(
                        "Found multiple verilog files/vtb cases for %s: %s and %s"
                        % (name, files[name]["verilog"], design["VERILOG_FILE"])
                    )
                    return 1
                design["VERILOG_FILE"] = files[name]["verilog"]
                design["TEST_FILES"] = files[name]["vtb"]
                design_name = name
        if design_name is None:
            # If VERILOG_FILE exists, default to using this.
            if "VERILOG_FILE" in design:
                # Just take the original design name
                design_name = design["ORIGINAL_DESIGN_NAME"]
                verilog_file = path.join(design_dir, design["VERILOG_FILE"])
                log.warn(
                    "No pytest files found for any of %s, defaulting to verilog file %s",
                    design["DESIGN_NAME"],
                    verilog_file,
                )
                # Don't pop synth parameters but change it to the right format
                design["SYNTH_PARAMETERS"] = " ".join(
                    f"{k}={v}" for k, v in design.get("SYNTH_PARAMETERS", {}).items()
                )
                # Run verilator on the verilog file
                design["VERILOG_FILE"] = path.join(build, f"{design_name}.v")
                run(
                    f"cd {root_dir()} && verilator -E -P {verilog_file} -Isrc > {design['VERILOG_FILE']}"
                )
                design["DESIGN_NAME"] = design_name
                design.pop("ORIGINAL_DESIGN_NAME")
            else:
                spinner.fail(
                    f"No verilog file found matching any of {design['DESIGN_NAME']}",
                )
                return 1
        else:
            # Success, remove synth parameters
            design.pop("ORIGINAL_DESIGN_NAME")
            if "SYNTH_PARAMETERS" in design:
                design.pop("SYNTH_PARAMETERS")
            design["DESIGN_NAME"] = design_name

    spinner.succeed("Finished collecting design files")

    return 0


def synthesize(design, path_prefix, args):
    log.info("Running synthesis on %s", design["DESIGN_NAME"])
    prefixed_design_name = f"{path_prefix}_{design['DESIGN_NAME']}"
    # Run synthesis
    synth_result = run(
        f"cd {caravel_dir()} && make {prefixed_design_name}",
        warn=True,
        hide=args.verbose == 0,
    )
    if synth_result.exited != 0:
        log.error("Synthesis failed for %s", design["DESIGN_NAME"])
        if args.verbose == 0:
            # Log the stdout and stderr
            log.error(synth_result.stdout)
            log.error(synth_result.stderr)
        return 1

    return 0


# Synthesize user project wrapper given an existing macro for a design.
# Also generates gate-level tests from test case files.
def synthesize_core(design, path_prefix, args):
    prefixed_design_name = f"{path_prefix}_{design['DESIGN_NAME']}"

    # First, clean up the existing user_project_wrapper
    spinner = Spinner(args, f"Copying files to user_project_wrapper")

    remote_rtl_dir = path.join(caravel_dir(), "verilog", "rtl")
    remote_openlane_dir = path.join(caravel_dir(), "openlane", "user_project_wrapper")
    build = build_dir()

    # Port mapping for the user_project_wrapper in verilog format
    port_mapping = ",\n\t\t".join(f".{k}({v})" for k, v in design["GPIO_MAP"].items())

    # Create user_project_wrapper.v in the build directory to copy over
    with open(path.join(build, "user_project_wrapper.v"), "w") as f:
        f.write(
            f"""
// SPDX-FileCopyrightText: 2020 Efabless Corporation
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// SPDX-License-Identifier: Apache-2.0

`default_nettype none
/*
 *-------------------------------------------------------------
 *
 * user_project_wrapper
 *
 * This wrapper enumerates all of the pins available to the
 * user for the user project.
 *
 * An example user project is provided in this wrapper.  The
 * example should be removed and replaced with the actual
 * user project.
 *
 *-------------------------------------------------------------
 */

module user_project_wrapper (
`ifdef USE_POWER_PINS
  inout vdda1,  // User area 1 3.3V supply
  inout vdda2,  // User area 2 3.3V supply
  inout vssa1,  // User area 1 analog ground
  inout vssa2,  // User area 2 analog ground
  inout vccd1,  // User area 1 1.8V supply
  inout vccd2,  // User area 2 1.8v supply
  inout vssd1,  // User area 1 digital ground
  inout vssd2,  // User area 2 digital ground
`endif

  // Wishbone Slave ports (WB MI A)
  input wb_clk_i,
  input wb_rst_i,
  input wbs_stb_i,
  input wbs_cyc_i,
  input wbs_we_i,
  input [3:0] wbs_sel_i,
  input [31:0] wbs_dat_i,
  input [31:0] wbs_adr_i,
  output wbs_ack_o,
  output [31:0] wbs_dat_o,

  // Logic Analyzer Signals
  input  [127:0] la_data_in,
  output [127:0] la_data_out,
  input  [127:0] la_oenb,

  // IOs
  input  [`MPRJ_IO_PADS-1:0] io_in,
  output [`MPRJ_IO_PADS-1:0] io_out,
  output [`MPRJ_IO_PADS-1:0] io_oeb,

  // Analog (direct connection to GPIO pad---use with caution)
  // Note that analog I/O is not available on the 7 lowest-numbered
  // GPIO pads, and so the analog_io indexing is offset from the
  // GPIO indexing by 7 (also upper 2 GPIOs do not have analog_io).
  inout [`MPRJ_IO_PADS-10:0] analog_io,

  // Independent clock (on independent integer divider)
  input user_clock2,

  // User maskable interrupt signals
  output [2:0] user_irq
);

  {prefixed_design_name} mprj (
`ifdef USE_POWER_PINS
    .VPWR(vccd1),  // User area 1 1.8V supply
    .VGND(vssd1),  // User area 1 digital ground
`endif
    {port_mapping}
  );

endmodule  // user_project_wrapper
"""
        )

    # Figure out whether inputs are io_in or io_out
    # This is done by looking at the port connections in thhe port mapping
    # and checking if a port in the index is `io_in` or `io_out`
    # Logic as follows:
    #  - If io_in for the gpio is used, default to USER_STD_INPUT_NOPULL
    #  - If io_out for the gpio is used, default to USER_STD_OUTPUT
    #  - If both io_in and io_out are used, default to USER_STD_BIDIRECTIONAL
    #  - If the port is manually specified in GPIO_CFG, use that value
    #  - Otherwise, default to MGMT_STD_OUTPUT

    # Counts whether this index was used in io_in or io_out
    gpio_in_used = set()
    gpio_out_used = set()
    for value in design["GPIO_MAP"].values():
        input_match = re.match(r"^io_in\[(\d+)\]$", value)
        output_match = re.match(r"^io_out\[(\d+)\]$", value)
        if input_match:
            gpio_in_used.add(int(input_match.group(1)))
        if output_match:
            gpio_out_used.add(int(output_match.group(1)))

    # GPIOs 0-4 are reserved for management SoC, throw an error if we try to configure them
    for gpio in range(0, 4):
        if gpio in design["GPIO_CFG"]:
            log.error(
                f"GPIO {gpio} is reserved for management SoC, cannot be configured by the user"
            )
            return 1

    gpio_cfg = [0] * (38 - 5)

    for gpio in range(5, 38):
        if gpio in design["GPIO_CFG"]:
            gpio_cfg[gpio - 5] = design["GPIO_CFG"][gpio]
        elif gpio in gpio_in_used and gpio in gpio_out_used:
            gpio_cfg[gpio - 5] = "USER_STD_BIDIRECTIONAL"
        elif gpio in gpio_in_used:
            gpio_cfg[gpio - 5] = "USER_STD_INPUT_NOPULL"
        elif gpio in gpio_out_used:
            gpio_cfg[gpio - 5] = "USER_STD_OUTPUT"
        else:
            gpio_cfg[gpio - 5] = "MGMT_STD_OUTPUT"

    gpio_cfg = "\n".join(
        [
            f"`define USER_CONFIG_GPIO_{gpio+5}_INIT `GPIO_MODE_{cfg}"
            for gpio, cfg in enumerate(gpio_cfg)
        ]
    )

    # Create user_defines.v to configure GPIO directions
    with open(path.join(build, "user_defines.v"), "w") as f:
        f.write(
            f"""
// SPDX-FileCopyrightText: 2022 Efabless Corporation
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// SPDX-License-Identifier: Apache-2.0

`default_nettype none

`ifndef __USER_DEFINES_H
// User GPIO initial configuration parameters
`define __USER_DEFINES_H

// deliberately erroneous placeholder value; user required to config GPIO's to other
`define GPIO_MODE_INVALID 13'hXXXX

// Authoritive source of these MODE defs is: caravel/verilog/rtl/user_defines.v
// Useful GPIO mode values.  These match the names used in defs.h.
//
`define GPIO_MODE_MGMT_STD_INPUT_NOPULL 13'h0403
`define GPIO_MODE_MGMT_STD_INPUT_PULLDOWN 13'h0c01
`define GPIO_MODE_MGMT_STD_INPUT_PULLUP 13'h0801
`define GPIO_MODE_MGMT_STD_OUTPUT 13'h1809
`define GPIO_MODE_MGMT_STD_BIDIRECTIONAL 13'h1801
`define GPIO_MODE_MGMT_STD_ANALOG 13'h000b

`define GPIO_MODE_USER_STD_INPUT_NOPULL 13'h0402
`define GPIO_MODE_USER_STD_INPUT_PULLDOWN 13'h0c00
`define GPIO_MODE_USER_STD_INPUT_PULLUP 13'h0800
`define GPIO_MODE_USER_STD_OUTPUT 13'h1808
`define GPIO_MODE_USER_STD_BIDIRECTIONAL 13'h1800
`define GPIO_MODE_USER_STD_OUT_MONITORED 13'h1802
`define GPIO_MODE_USER_STD_ANALOG 13'h000a

// The power-on configuration for GPIO 0 to 4 is fixed and cannot be
// modified (allowing the SPI and debug to always be accessible unless
// overridden by a flash program).

// The values below can be any of the standard types defined above,
// or they can be any 13-bit value if the user wants a non-standard
// startup state for the GPIO.  By default, every GPIO from 5 to 37
// is set to power up as an input controlled by the management SoC.
// Users may want to redefine these so that the user project powers
// up in a state that can be used immediately without depending on
// the management SoC to run a startup program to configure the GPIOs.

{gpio_cfg}

`endif  // __USER_DEFINES_H
"""
        )

    # Copy the user_project_wrapper files to caravel
    cp(
        path.join(build, "user_project_wrapper.v"),
        path.join(remote_rtl_dir, "user_project_wrapper.v"),
    )

    cp(
        path.join(build, "user_defines.v"),
        path.join(remote_rtl_dir, "user_defines.v"),
    )

    # create macro.cfg and copy to caravel
    with open(path.join(build, "macro.cfg"), "w") as f:
        f.write(f"mprj {design['MPRJ_POS']}")

    cp(
        path.join(build, "macro.cfg"),
        path.join(remote_openlane_dir, "macro.cfg"),
    )

    openlane_config = {
        "DESIGN_NAME": "user_project_wrapper",
        "VERILOG_FILES": [
            "dir::../../verilog/rtl/defines.v",
            "dir::../../verilog/rtl/user_project_wrapper.v",
        ],
        "ROUTING_CORES": 1,
        "CLOCK_PERIOD": design["PARAMS"]["CLOCK_PERIOD"],
        "CLOCK_PORT": "wb_clk_i",
        "CLOCK_NET": "mprj.clk",
        "FP_PDN_MACRO_HOOKS": "mprj vccd1 vssd1 vccd1 vssd1",
        "MACRO_PLACEMENT_CFG": "dir::macro.cfg",
        "MAGIC_DEF_LABELS": 0,
        "VERILOG_FILES_BLACKBOX": [f"dir::../../verilog/gl/{prefixed_design_name}.v"],
        "EXTRA_LEFS": f"dir::../../lef/{prefixed_design_name}.lef",
        "EXTRA_GDS_FILES": f"dir::../../gds/{prefixed_design_name}.gds",
        "EXTRA_LIBS": f"dir::../../lib/{prefixed_design_name}.lib",
        "EXTRA_SPEFS": [
            prefixed_design_name,
            f"dir::../../spef/multicorner/{prefixed_design_name}.min.spef",
            f"dir::../../spef/multicorner/{prefixed_design_name}.nom.spef",
            f"dir::../../spef/multicorner/{prefixed_design_name}.max.spef",
        ],
        "BASE_SDC_FILE": "dir::base_user_project_wrapper.sdc",
        "IO_SYNC": 0,
        "MAX_TRANSITION_CONSTRAINT": 1.5,
        "RUN_LINTER": 0,
        "QUIT_ON_SYNTH_CHECKS": 0,
        "FP_PDN_CHECK_NODES": 0,
        "SYNTH_ELABORATE_ONLY": 1,
        "PL_RANDOM_GLB_PLACEMENT": 1,
        "PL_RESIZER_DESIGN_OPTIMIZATIONS": 0,
        "PL_RESIZER_TIMING_OPTIMIZATIONS": 0,
        "GLB_RESIZER_DESIGN_OPTIMIZATIONS": 0,
        "GLB_RESIZER_TIMING_OPTIMIZATIONS": 0,
        "PL_RESIZER_BUFFER_INPUT_PORTS": 0,
        "FP_PDN_ENABLE_RAILS": 0,
        "GRT_REPAIR_ANTENNAS": 0,
        "RUN_FILL_INSERTION": 0,
        "RUN_TAP_DECAP_INSERTION": 0,
        "FP_PDN_VPITCH": 180,
        "FP_PDN_HPITCH": 180,
        "RUN_CTS": 0,
        "FP_PDN_VOFFSET": 5,
        "FP_PDN_HOFFSET": 5,
        "MAGIC_ZEROIZE_ORIGIN": 0,
        "FP_SIZING": "absolute",
        "RUN_CVC": 0,
        "UNIT": 2.4,
        "FP_IO_VEXTEND": "expr::2 * $UNIT",
        "FP_IO_HEXTEND": "expr::2 * $UNIT",
        "FP_IO_VLENGTH": "expr::$UNIT",
        "FP_IO_HLENGTH": "expr::$UNIT",
        "FP_IO_VTHICKNESS_MULT": 4,
        "FP_IO_HTHICKNESS_MULT": 4,
        "FP_PDN_CORE_RING": 1,
        "FP_PDN_CORE_RING_VWIDTH": 3.1,
        "FP_PDN_CORE_RING_HWIDTH": 3.1,
        "FP_PDN_CORE_RING_VOFFSET": 12.45,
        "FP_PDN_CORE_RING_HOFFSET": 12.45,
        "FP_PDN_CORE_RING_VSPACING": 1.7,
        "FP_PDN_CORE_RING_HSPACING": 1.7,
        "FP_PDN_VWIDTH": 3.1,
        "FP_PDN_HWIDTH": 3.1,
        "FP_PDN_VSPACING": "expr::(5 * $FP_PDN_CORE_RING_VWIDTH)",
        "FP_PDN_HSPACING": "expr::(5 * $FP_PDN_CORE_RING_HWIDTH)",
        "VDD_NETS": ["vccd1", "vccd2", "vdda1", "vdda2"],
        "GND_NETS": ["vssd1", "vssd2", "vssa1", "vssa2"],
        "SYNTH_USE_PG_PINS_DEFINES": "USE_POWER_PINS",
        "pdk::sky130*": {
            "RT_MAX_LAYER": "met4",
            "DIE_AREA": "0 0 2920 3520",
            "FP_DEF_TEMPLATE": "dir::fixed_dont_change/user_project_wrapper.def",
            "scl::sky130_fd_sc_hd": {"CLOCK_PERIOD": 25},
            "scl::sky130_fd_sc_hdll": {"CLOCK_PERIOD": 10},
            "scl::sky130_fd_sc_hs": {"CLOCK_PERIOD": 8},
            "scl::sky130_fd_sc_ls": {"CLOCK_PERIOD": 10, "SYNTH_MAX_FANOUT": 5},
            "scl::sky130_fd_sc_ms": {"CLOCK_PERIOD": 10},
        },
        "pdk::gf180mcuC": {
            "STD_CELL_LIBRARY": "gf180mcu_fd_sc_mcu7t5v0",
            "FP_PDN_CHECK_NODES": 0,
            "FP_PDN_ENABLE_RAILS": 0,
            "RT_MAX_LAYER": "Metal4",
            "DIE_AREA": "0 0 3000 3000",
            "FP_DEF_TEMPLATE": "dir::fixed_dont_change/user_project_wrapper_gf180mcu.def",
            "PL_OPENPHYSYN_OPTIMIZATIONS": 0,
            "DIODE_INSERTION_STRATEGY": 0,
            "MAGIC_WRITE_FULL_LEF": 0,
        },
    }

    # Write the openlane config.json
    config_json = path.join(build, f"user_project_wrapper_config.json")
    with open(config_json, "w") as f:
        json.dump(openlane_config, f, indent=2)

    cp(
        config_json,
        path.join(remote_openlane_dir, "config.json"),
    )

    spinner.succeed("Finished copying files to user_project_wrapper")
    spinner = Spinner(
        args, f"Synthesizing user_project_wrapper with design {prefixed_design_name}"
    )

    # Run synthesis
    synth_result = run(
        f"cd {caravel_dir()} && make user_project_wrapper",
        warn=True,
        hide=args.verbose == 0,
    )

    if synth_result.exited != 0:
        log.error("Synthesis failed for user_project_wrapper")
        if args.verbose == 0:
            # Log the stdout and stderr
            log.error(synth_result.stdout)
            log.error(synth_result.stderr)
        return 1

    # TODO: Add gl tests

    spinner.succeed("Finished synthesizing user project wrapper")
    return 0


# Propogate config variables through a design
def propogate(designs: dict) -> list[dict]:
    def propogate_rec(designs: dict, namespace: dict):
        # This is an actual design
        log.debug("Propogating %s", designs)
        if "DESIGNS" not in designs:
            return [merge_dict(namespace, designs)]
        # Take out the "DESIGNS" key
        next = designs.pop("DESIGNS")

        # Make sure that designs is a list of dicts
        if not isinstance(next, list) or any(not isinstance(d, dict) for d in next):
            log.error(
                "Invalid format for config file, DESIGNS should contain a list of designs"
            )

        # Add names from the current scope to the namespace
        namespace = merge_dict(namespace, designs)
        return sum([propogate_rec(design, namespace) for design in next], [])

    return propogate_rec(designs, {})


class Synth(SubCommand):
    def name():
        return "synth"

    def args(subparsers):
        args = subparsers.add_parser("synth", help="Run synthesis on a design")

        args.add_argument(
            "design",
            metavar="Design",
            type=str,
            help="Design to run synthesis on (a .yml or .json file)",
        )

        args.add_argument(
            "-d",
            "--dir",
            metavar="Directory",
            type=str,
            default="build",
            help="Directory to save synthesis results to",
        )

        args.add_argument(
            "-n",
            "--nthreads",
            metavar="Number of Threads",
            type=multi_type(
                positive_int, "auto"
            ),  # expect an integer or the string 'auto'
            default="auto",
            help="Number of threads to use for synthesis. Use 'auto' to use a threadcount equal to the number of CPU cores.",
        )

    def run(args):
        """Run synthesis on a design."""
        if not caravel_installed():
            log.error("Caravel not yet installed, run `caravel install` first.")
            return 1

        log.info("Running synthesis on %s", args.design)

        # ----------------------------------------------------------------
        # Load the design file and propogate the configuration variables
        # ----------------------------------------------------------------
        designs = propogate(load_config(args.design))

        # Move all keys other than a select few into the params dict
        special_keys = set(
            [
                "DESIGN_NAME",
                "TEST_FILES",
                "FP_PIN_ORDER_CFG",
                "SYNTH_PARAMETERS",
                "VERILOG_FILE",
                "DESIGN_IS_CORE",
                "GPIO_MAP",
                "GPIO_CFG",
                "MPRJ_POS",
            ]
        )
        # Move everything other than certain special keys into the PARAMS area
        designs = [
            {
                **{k: v for k, v in design.items() if k in special_keys},
                "PARAMS": {k: v for k, v in design.items() if k not in special_keys},
            }
            for design in designs
        ]

        # If any designs are CORE, we can only synthesize one user_project_wrapper at a time so we should make sure there is only one design total.

        if any(design.get("DESIGN_IS_CORE", 1) == 1 for design in designs):
            if len(designs) > 1:
                log.error(
                    "Found multiple core designs, can only synthesize one user_project_wrapper at a time"
                )
                return 1

            if "GPIO_MAP" not in designs[0]:
                log.error("Core design found but no gpio mapping (GPIO_MAP) specified.")
                return 1
            if "MPRJ_POS" not in designs[0]:
                log.error(
                    "Core design found but no mprj macro position (MPRJ_POS) specified."
                )
                return 1

        log.info("Synthesizing %s designs", len(designs))
        log.debug(json.dumps(designs, indent=2))

        # ----------------------------------------------------------------
        # Collect the design files
        # ----------------------------------------------------------------
        # create a temporary build directory for saving files
        build = build_dir()

        err_code = design_files(build, designs, args)
        if err_code:
            return err_code

        log.debug("Synthesizing designs\n%s", json.dumps(designs, indent=2))

        # path prefix for design files
        path_prefix = path.relpath(
            path.dirname(args.design), path.join(root_dir(), "src")
        )
        path_prefix = "_".join(split_path(path_prefix))
        log.debug("Adding path prefix %s to designs", path_prefix)

        # ----------------------------------------------------------------
        # Copy files to remote
        # ----------------------------------------------------------------
        spinner = Spinner(args, "Copying files to caravel")
        design_dir = path.abspath(path.dirname(args.design))
        remote_rtl_dir = path.join(caravel_dir(), "verilog", "rtl")
        remote_openlane_dir = path.join(caravel_dir(), "openlane")
        for design in designs:
            prefixed_design_name = f"{path_prefix}_{design['DESIGN_NAME']}"
            openlane_project_dir = path.join(remote_openlane_dir, prefixed_design_name)
            # Create the openlane project directory
            run(f"mkdir -p {openlane_project_dir}")

            # Replace the top module name in the verilog file
            with open(design["VERILOG_FILE"], "r") as f:
                verilog = f.read()

            # Replace the top module name
            verilog = re.sub(
                f"module\\s+{re.escape(design['DESIGN_NAME'])}",
                f"module {prefixed_design_name}",
                verilog,
                flags=re.MULTILINE,
            )

            # Write the verilog file
            with open(design["VERILOG_FILE"], "w") as f:
                f.write(verilog)

            # Copy files to caravel
            cp(
                design["VERILOG_FILE"],
                path.join(remote_rtl_dir, f"{prefixed_design_name}.sv"),
            )
            # Run sv2v on the verilog file
            run(
                f"cd {remote_rtl_dir} && /classes/c2s2/install/stow-pkgs/x86_64-rhel7/bin/sv2v -w adjacent {prefixed_design_name}.sv"
            )

            # Write the openlane config.json
            config_json = path.join(build, f"{prefixed_design_name}_config.json")
            with open(config_json, "w") as f:
                json.dump(
                    {
                        "DESIGN_NAME": prefixed_design_name,
                        "VERILOG_FILES": [
                            f"dir::../../verilog/rtl/{prefixed_design_name}.v"
                        ],
                        "DESIGN_IS_CORE": 0,
                        "FP_PIN_ORDER_CFG": "dir::pin_order.cfg",
                        **design["PARAMS"],
                    },
                    f,
                    indent=2,
                )

            cp(
                config_json,
                path.join(openlane_project_dir, "config.json"),
            )
            cp(
                path.join(design_dir, design["FP_PIN_ORDER_CFG"]),
                path.join(openlane_project_dir, "pin_order.cfg"),
            )

            # TODO: Copy the test files

        spinner.succeed("Finished copying files to caravel")

        # ----------------------------------------------------------------
        # Run synthesis
        # ----------------------------------------------------------------

        # create the output directory
        os.makedirs(path.join(root_dir(), args.dir), exist_ok=True)

        # Create threadpool
        if args.nthreads == "auto":
            threads = multiprocessing.cpu_count()
        else:
            threads = args.nthreads

        spinner = Spinner(args, f"Running macro synthesis with {threads} threads")

        with multiprocessing.Pool(threads) as pool:
            results = pool.starmap(
                synthesize, [(design, path_prefix, args) for design in designs]
            )
            if any(results):
                spinner.fail("Synthesis failed")
                log.error(
                    "Synthesis failed for the following designs:\n\t%s",
                    "\n\t".join(
                        [
                            path.join(
                                caravel_link(),
                                "openlane",
                                f"{path_prefix}_{design['DESIGN_NAME']}",
                            )
                            for design, result in zip(designs, results)
                            if result
                        ]
                    ),
                )
                return 1

        spinner.succeed("Finished macro synthesis")

        # If there is a core design, run synthesis on the user_project_wrapper
        if designs[0].get("DESIGN_IS_CORE", 1) == 1:
            synthesize_core(designs[0], path_prefix, args)

        return 0
