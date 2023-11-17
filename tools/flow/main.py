#!/usr/bin/env python
from utils.config import get_user
from utils.remote import connect as connect_native
from utils.utils import setup_logging
from os import path
import logging as log
import utils.cmdline as cmdline
from fabric import Connection


def caravel_dir():
    return path.join("/scratch", "caravel", get_user())


def connect():
    connection = connect_native()

    # Install if necessary
    exists = connection.run(
        f'if [ ! -d "{caravel_dir()}" ]; then false; fi;', warn=True
    )
    if exists.exited != 0:
        install(connection)

    return connection


def install(connection: Connection, force: bool = False):
    """Install caravel in a custom location."""
    log.info("Installing caravel in %s", caravel_dir())

    if force:
        connection.run(f"rm -rf {caravel_dir()}")
    else:
        # Check if the directory exists and exit if it does
        exists = connection.run(
            f'if [ -d "{caravel_dir()}" ]; then true; fi;', warn=True
        )
        if exists.exited != 0:
            log.error(
                "The caravel directory already exists. Use --force to overwrite it."
            )
            exit(1)

    connection.run(f"mkdir -p {caravel_dir()}")
    connection.run(
        f"""
cd {caravel_dir()} && \
    git clone --depth 1 --branch mpw-9g https://github.com/efabless/caravel_user_project.git . && \
    make install check-env install_mcw setup-timing-scripts
"""
    )


if __name__ == "__main__":
    parser = cmdline.Parser(description="Custom script to run the flow.")

    parser.add_argument(
        "-v", "--verbose", action="count", default=0, help="Increase logging level"
    )

    subparsers = parser.add_subparsers(dest="command")

    install_args = subparsers.add_parser("install", help="Install caravel")

    install_args.add_argument(
        "-f",
        "--force",
        action="store_true",
        default=False,
        help="Overwrite existing caravel installation",
    )

    args = parser.parse_args()

    setup_logging(args)
    connection = connect()
    if args.command == "install":
        install(connection, args.force)
