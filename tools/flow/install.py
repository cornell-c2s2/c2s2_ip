# install caravel
from utils.cmdline import SubCommand
from utils.invoke import caravel_dir, caravel_installed, run
import logging as log


class Install(SubCommand):
    def name():
        return "install"

    def args(subparsers):
        args = subparsers.add_parser("install", help="Install caravel")

        args.add_argument(
            "-f",
            "--force",
            action="store_true",
            default=False,
            help="Overwrite existing caravel installation",
        )

    def run(args):
        """Install caravel in a custom location."""

        # Check if caravel is installed
        if not args.force and caravel_installed():
            log.error(
                "Caravel is already installed. Run `caravel install --force` to reinstall."
            )
            return 1

        log.info("Installing caravel in %s", caravel_dir())

        run(f"rm -rf {caravel_dir()} && mkdir -p {caravel_dir()}")
        run(
            f"""
cd {caravel_dir()} && \
    git clone --depth 1 --branch mpw-9g https://github.com/efabless/caravel_user_project.git . && \
    make install check-env install_mcw setup-timing-scripts
"""
        )
