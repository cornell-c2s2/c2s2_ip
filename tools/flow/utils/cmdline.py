import argparse
import sys


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
