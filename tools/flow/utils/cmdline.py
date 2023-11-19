from abc import abstractmethod
import argparse
import sys
from fabric import Connection


def positive_int(value):
    value = int(value)
    if value <= 0:
        raise argparse.ArgumentTypeError("Expected positive integer")
    return value


# Multitypes for argparse
# Allows an argument to be one of multiple types
# If an argument is not a function, it will be treated as an equality check
def multi_type(*args):
    def check_type(value):
        nonlocal args
        for arg in args:
            if callable(arg):
                try:
                    return arg(value)
                except Exception:
                    pass
            else:
                if arg == value:
                    return value
        raise argparse.ArgumentTypeError(
            "Invalid type for argument, expected one of {}".format(args)
        )

    return check_type


class Parser(argparse.ArgumentParser):
    def error(self, message):
        sys.stderr.write("error: %s\n" % message)
        self.print_help()
        sys.exit(2)

    def parse_args(self, *args, **kwargs):
        if len(sys.argv) == 1:
            self.print_help()
            sys.exit(2)
        args = super(Parser, self).parse_args(*args, **kwargs)
        return args


# Abstract class representing a subcommand
# Requires implementers to define an args function and a run function
class SubCommand:
    @staticmethod
    @abstractmethod
    # Return the name of the subcommand
    def name() -> str:
        pass

    @staticmethod
    @abstractmethod
    # Add arguments to the subparser
    def args(subparsers: argparse._SubParsersAction) -> None:
        pass

    @staticmethod
    @abstractmethod
    # Must return an integer representing the exit code
    def run(connection: Connection, args: argparse.Namespace) -> int:
        pass
