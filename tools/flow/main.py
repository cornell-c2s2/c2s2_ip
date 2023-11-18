#!/usr/bin/env python
from utils.remote import connect
from tools.flow.utils.logging import setup_logging
from os import path
import logging as log
import utils.cmdline as cmdline
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
            err_code = subcommand.run(connection, args)
            if err_code:
                log.error(
                    "Subcommand %s failed with error code %d", args.command, err_code
                )
            break

    connection.close()
