# Push a file through caravel synthesis (openlane)
from utils.remote import caravel_dir, caravel_installed, connect
from utils.cmdline import SubCommand, multi_type, positive_int
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
import multiprocessing


# Take a list of designs and collect the design files for them
def design_files(build_dir: str, designs: list[dict], args) -> list[dict]:
    # ----------------------------------------------------------------
    # Run pytest to generate the designs
    # ----------------------------------------------------------------
    # get only the name of the build directory
    build_dir_name = path.basename(build_dir)

    spinner = Spinner(args, f"Running pytest in {build_dir} to generate verilog files")

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


def synth_results(connection, build_dir, design_name: str, args):
    # ----------------------------------------------------------------
    # Copy the results back
    # ----------------------------------------------------------------

    log.info("Saving synthesis results for %s to %s", design_name, build_dir)
    # First, zip the results
    connection.run(
        f"cd {path.join(caravel_dir(), "openlane", design_name, "runs")} && zip -r results.zip {design_name}",
        hide=args.verbose < 2,
    )

    # Then, copy the results back
    connection.get(
        path.join(
            caravel_dir(),
            "openlane",
            design_name,
            "runs",
            "results.zip",
        ),
        path.join(build_dir, f"{design_name}.zip"),
    )

    # Delete the results on the server
    connection.run(
        f"rm {path.join(caravel_dir(), "openlane", design_name, "runs", "results.zip")}"
    )

    # Unzip the results
    subprocess.run(
        ["unzip", "-o", path.join(build_dir, f"{design_name}.zip"), "-d", build_dir],
        stdout=subprocess.DEVNULL if args.verbose < 2 else None,
    )

    # Delete the zip file
    os.remove(path.join(build_dir, f"{design_name}.zip"))

def synthesize(design, path_prefix, args):
    # Create a new connection as this is running in a separate thread
    connection = connect()

    log.info("Running synthesis on %s", design["DESIGN_NAME"])
    prefixed_design_name = f"{path_prefix}_{design['DESIGN_NAME']}"
    # Run synthesis
    synth_result = connection.run(
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
        synth_results(connection, path.join(root_dir(), args.dir), prefixed_design_name, args)
        connection.close()
        return 1

    # Copy the results back
    synth_results(connection, path.join(root_dir(), args.dir), prefixed_design_name, args)

    connection.close()

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
            type=multi_type(positive_int, 'auto'), # expect an integer or the string 'auto'
            default=1,
            help="Number of threads to use for synthesis. Use 'auto' to use a threadcount equal to the number of CPU cores.",
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
            prefix="build", dir=root_dir(), delete=False
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
        
        # ----------------------------------------------------------------
        # Run synthesis
        # ----------------------------------------------------------------

        # create the output directory
        os.makedirs(path.join(root_dir(), args.dir), exist_ok=True)

        # Create threadpool
        if args.threads == 'auto':
            threads = multiprocessing.cpu_count()
        else:
            threads = args.threads

        spinner = Spinner(args, f"Running synthesis with {threads} threads...")
        
        with multiprocessing.Pool(threads) as pool:
            results = pool.starmap(synthesize, [(design, path_prefix, args) for design in designs])
            if any(results):
                log.error("Synthesis failed for the following designs:")
                for design, result in zip(designs, results):
                    if result:
                        log.error(design["DESIGN_NAME"])
                return 1
        
        spinner.succeed("Finished synthesis")

        # ----------------------------------------------------------------
        # Cleanup
        # ----------------------------------------------------------------
        build_dir.cleanup()

        return 0
