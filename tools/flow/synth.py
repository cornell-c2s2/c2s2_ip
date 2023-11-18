# Push a file through caravel synthesis (openlane)
from utils.remote import caravel_dir, caravel_installed
from utils.cmdline import SubCommand
import logging as log
from utils.misc import load_config, merge_dict, root_dir, split_path
from utils.logging import Spinner
import json
import subprocess
from os import path
import os
import tempfile
import itertools
import re


# Take a list of designs and collect the design files for them
def design_files(build_dir: str, designs: list[dict], args) -> list[dict]:
    # ----------------------------------------------------------------
    # Run pytest to generate the designs
    # ----------------------------------------------------------------
    log.info("Running pytest in %s", build_dir)
    # get only the name of the build directory
    build_dir_name = path.basename(build_dir)

    spinner = Spinner(args, "Running pytest to generate verilog files")

    design_dir = path.dirname(args.design)
    # get the pytest files
    pytest_files = set(sum([design["TEST_FILES"] for design in designs], []))
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
            build_dir_name,
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
            f"{k}_{v}" for k, v in design.pop("SYNTH_PARAMETERS", {}).items()
        ]
        # get possible design names (permutations of parameters)
        top_module = design["DESIGN_NAME"]
        design["DESIGN_NAME"] = set()
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
    verilog_files: dict[str, str] = {}
    vtb_files: dict[str, list[str]] = {}

    for root, _, files in os.walk(build_dir):
        for file in files:
            # Check if the file is a verilog file matching
            # DESIGNNAME__pickled.v
            match = verilog_file_regex.match(file)
            if match is not None:
                design_name = match.group("design_name")
                if design_name in verilog_files:
                    log.error(
                        "Found multiple verilog files for %s: %s and %s",
                        design_name,
                        verilog_files[design_name],
                        path.join(root, file),
                    )
                    return 1
                verilog_files[design_name] = path.join(root, file)
            match = vtb_file_regex.match(file)
            if match is not None:
                design_name = match.group("design_name")
                if design_name not in vtb_files:
                    vtb_files[design_name] = []
                vtb_files[design_name].append(path.join(root, file))

    log.debug("Collected verilog files %s", verilog_files)
    log.debug("Collected vtb files %s", vtb_files)

    # merge verilog and vtb files into one dict
    files: dict[str, dict[str, str]] = {}
    for design_name in verilog_files.keys():
        if design_name not in vtb_files:
            log.error("No corresponding vtb cases found for %s", design_name)
            return 1
        files[design_name] = {
            "verilog": verilog_files[design_name],
            "vtb": vtb_files.pop(design_name),
        }

    if len(vtb_files) > 0:
        log.error("Found extra vtb files not matching any verilog files: %s", vtb_files)
        return 1

    # delete these from the scope so they don't get used later
    del verilog_files
    del vtb_files

    # match the verilog files to the designs
    for design in designs:
        design_name = None
        for name in design["DESIGN_NAME"]:
            if name in files:
                if design_name is not None:
                    log.error(
                        "Found multiple verilog files/vtb cases for %s: %s and %s",
                        name,
                        files[name]["verilog"],
                        design["VERILOG_FILE"],
                    )
                    return 1
                design["VERILOG_FILE"] = files[name]["verilog"]
                design["TEST_FILES"] = files[name]["vtb"]
                design_name = name
        if design_name is None:
            log.error("No verilog file found matching any of %s", design["DESIGN_NAME"])
            return 1
        design["DESIGN_NAME"] = design_name

    spinner.succeed("Finished collecting design files")

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

    def run(connection, args):
        """Run synthesis on a design."""
        if not caravel_installed(connection):
            log.error("Caravel not yet installed, run `caravel install` first.")
            return 1

        log.info("Running synthesis on %s", args.design)

        # ----------------------------------------------------------------
        # Load the design file and propogate the configuration variables
        # ----------------------------------------------------------------
        designs = propogate(load_config(args.design))

        # Move all keys other than a select few into the params dict
        special_keys = set(
            ["DESIGN_NAME", "TEST_FILES", "FP_PIN_ORDER_CFG", "SYNTH_PARAMETERS"]
        )
        designs = [
            {
                **{k: v for k, v in design.items() if k in special_keys},
                "PARAMS": {k: v for k, v in design.items() if k not in special_keys},
            }
            for design in designs
        ]

        log.info("Synthesizing %s designs", len(designs))
        log.debug(json.dumps(designs, indent=2))

        # ----------------------------------------------------------------
        # Collect the design files
        # ----------------------------------------------------------------
        # create a temporary build directory for saving files
        build_dir = tempfile.TemporaryDirectory(
            prefix="build", dir=root_dir(), delete=args.verbose == 0
        )

        err_code = design_files(build_dir.name, designs, args)
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
        design_dir = path.dirname(args.design)
        remote_rtl_dir = path.join(caravel_dir(), "verilog", "rtl")
        remote_openlane_dir = path.join(caravel_dir(), "openlane")
        for design in designs:
            prefixed_design_name = f"{path_prefix}_{design['DESIGN_NAME']}"
            openlane_project_dir = path.join(remote_openlane_dir, prefixed_design_name)
            # Create the openlane project directory
            connection.run(f"mkdir -p {openlane_project_dir}")

            # Copy the verilog file
            connection.put(
                design["VERILOG_FILE"],
                path.join(remote_rtl_dir, f"{prefixed_design_name}.sv"),
            )
            # Run sv2v on the verilog file
            connection.run(
                f"cd {remote_rtl_dir} && /classes/c2s2/install/stow-pkgs/x86_64-rhel7/bin/sv2v -w adjacent {prefixed_design_name}.sv"
            )

            # Write the openlane config.json
            config_json = path.join(
                build_dir.name, f"{prefixed_design_name}_config.json"
            )
            with open(config_json, "w") as f:
                json.dump(
                    {
                        "DESIGN_NAME": prefixed_design_name,
                        "VERILOG_FILES": [
                            f"dir::../../verilog/rtl/{prefixed_design_name}.v"
                        ],
                        "FP_PIN_ORDER_CFG": "dir::pin_order.cfg",
                        **design["PARAMS"],
                    },
                    f,
                )

            connection.put(
                config_json,
                path.join(openlane_project_dir, "config.json"),
            )
            connection.put(
                path.join(design_dir, design["FP_PIN_ORDER_CFG"]),
                path.join(openlane_project_dir, "pin_order.cfg"),
            )

            # TODO: Copy the test files

        spinner.succeed("Finished copying files to caravel")

        spinner = Spinner(args, "Running synthesis...")

        for i, design in enumerate(designs):
            spinner.rename(
                f"Running synthesis [{i/len(designs)*100:.0f}%] [{design['DESIGN_NAME']}]"
            )
            prefixed_design_name = f"{path_prefix}_{design['DESIGN_NAME']}"
            # Run synthesis
            connection.run(f"cd {caravel_dir()} && make {prefixed_design_name}")

        # ----------------------------------------------------------------
        # Cleanup
        # ----------------------------------------------------------------
        # Clean up if log level is not debug
        if args.verbose == 0:
            build_dir.cleanup()

        return 0
