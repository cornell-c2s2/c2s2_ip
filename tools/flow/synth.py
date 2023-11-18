# Push a file through caravel synthesis (openlane)
from utils.cmdline import SubCommand
import logging as log
from utils.file import load_config, root
import json
import subprocess
from os import path
import tempfile


# Propogate config variables through a design
def propogate(designs: dict) -> list[dict]:
    def propogate_rec(designs: dict, namespace: dict):
        # This is an actual design
        log.debug("Propogating %s", designs)
        if "DESIGNS" not in designs:
            return [{**namespace, **designs}]
        # Take out the "DESIGNS" key
        next = designs.pop("DESIGNS")

        # Make sure that designs is a list of dicts
        if not isinstance(next, list) or any(not isinstance(d, dict) for d in next):
            log.error(
                "Invalid format for config file, DESIGNS should contain a list of designs"
            )

        # Add names from the current scope to the namespace
        namespace = {**namespace, **designs}
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

        log.info("Running synthesis on %s", args.design)

        # ----------------------------------------------------------------
        # Load the design file and propogate the configuration variables
        # ----------------------------------------------------------------
        designs = propogate(load_config(args.design))

        # ----------------------------------------------------------------
        # Run pytest to generate the designs
        # ----------------------------------------------------------------

        # create a temporary build directory for pytest
        build_dir = tempfile.TemporaryDirectory(
            prefix="build", dir=root(), delete=args.verbose == 0
        )
        log.info("Running pytest in %s", build_dir.name)
        # get only the name of the build directory
        build_dir_name = path.basename(build_dir.name)

        design_dir = path.dirname(args.design)
        subprocess.run(
            [
                "pytest",
                design_dir,
                "-n",
                "auto",
                "--test-verilog",
                "--dump-vtb",
                "--build-dir",
                build_dir_name,
            ]
            + ["-v"]
            if args.verbose > 0
            else [],
        )

        log.info("Synthesizing %s designs", len(designs))
        log.debug(json.dumps(designs, indent=2))

        # ----------------------------------------------------------------
        # Cleanup
        # ----------------------------------------------------------------
        # Clean up if log level is not debug
        if args.verbose == 0:
            build_dir.cleanup()
