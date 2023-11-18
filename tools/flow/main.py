#!/usr/bin/env python
from utils.config import get_user
from utils.remote import connect
from tools.flow.utils.logging import setup_logging
from os import path
import logging as log
import utils.cmdline as cmdline
from fabric import Connection
from install import Install
from synth import Synth

if __name__ == "__main__":
    parser = cmdline.Parser(description="Custom script to run the flow.")

    parser.add_argument(
        "-v", "--verbose", action="count", default=0, help="Increase logging level"
    )

    subparsers = parser.add_subparsers(dest="command")

    subcommands = [Install, Synth]

    # Add subcommand parsers
    for subcommand in subcommands:
        subcommand.args(subparsers)

    args = parser.parse_args()

    setup_logging(args)
    connection = connect()
    for subcommand in subcommands:
        if subcommand.name() == args.command:
            subcommand.run(connection, args)
            break

    connection.close()
