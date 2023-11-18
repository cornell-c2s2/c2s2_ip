from abc import abstractmethod
import argparse
import sys
from fabric import Connection


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
