# Helper file with utility functions
import logging as log
import sys


def setup_logging(args):
    # Add color to logs
    log.addLevelName(log.DEBUG, "\033[1;34m%s\033[1;0m" % log.getLevelName(log.DEBUG))
    log.addLevelName(log.INFO, "\033[1;32m%s\033[1;0m" % log.getLevelName(log.INFO))
    log.addLevelName(
        log.WARNING, "\033[1;33m%s\033[1;0m" % log.getLevelName(log.WARNING)
    )
    log.addLevelName(log.ERROR, "\033[1;31m%s\033[1;0m" % log.getLevelName(log.ERROR))

    # Set verbosity level.
    level = None
    if "verbose" not in args or args.verbose == 0:
        level = log.WARNING
    elif args.verbose == 1:
        level = log.INFO
    elif args.verbose >= 2:
        level = log.DEBUG

    log.basicConfig(format="%(levelname)s: %(message)s", stream=sys.stderr, level=level)
