#!/usr/bin/env python
#=========================================================================
# pickel.py [options] [interconnect_file]
#=========================================================================
#
#  -h --help           Display this message
#     --src            Directory of the source files (default: src)
#     --out            File to write extracted code (default: src_v/build/out.v)
#     --interconnect   File to start extraction (default: src/tapeins/sp24/tapein2/interconnect_fpga.v)
#
# Takes a verilog file and extracts all the `include files
# and writes them to a new file
#
# Author : Anjelica Bian (adopted from Christopher Batten)
# Date   : Nov 17, 2024
#

import argparse
import os, subprocess, sys, re
from typing import List

#-------------------------------------------------------------------------
# Command line processing
#-------------------------------------------------------------------------

class ArgumentParserWithCustomError(argparse.ArgumentParser):
  def error( self, msg = "" ):
    if ( msg ): print("\n ERROR: %s" % msg)
    print("")
    file = open( sys.argv[0] )
    for ( lineno, line ) in enumerate( file ):
      if ( line[0] != '#' ): sys.exit(msg != "")
      if ( (lineno == 2) or (lineno >= 4) ): print( line[1:].rstrip("\n") )

def parse_cmdline():
  p = ArgumentParserWithCustomError( add_help=False )

  p.add_argument( "-h", "--help",        action="store_true" )
  p.add_argument(       "--src",         type=str,   default=os.path.join(find_top_level(), "src") )
  p.add_argument(       "--out",         type=str,   default=os.path.join(find_top_level(), "src_v", "build", "out.v") )
  p.add_argument(       "--interconnect",type=str,   default=os.path.join(find_top_level(), "src", "tapeins/sp24/tapein2/interconnect_fpga.v") )


  opts = p.parse_args()
  if opts.help: p.error()
  return opts

#-------------------------------------------------------------------------
# Get includes
#-------------------------------------------------------------------------

tick_include = []

def add(list : List, item):
    if item not in list:
        list.append(item)

def find_tick_include(dir, file):
    with open(file, 'r') as f:
        for line in f:
            include = re.match(r'`include\s+"([\w/]+\.(s?v))"', line)
            if include:
                add(tick_include, include.group(1))
                recr_file = os.path.join(dir, include.group(1))
                find_tick_include(dir, recr_file)

def find_top_level():
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"], 
            capture_output=True, 
            text=True,
            check=True
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError:
        print("Not a Git repository")
        return None


#-------------------------------------------------------------------------
# Main
#-------------------------------------------------------------------------

if __name__ == "__main__":
    opts = parse_cmdline()
    
    find_tick_include(opts.src, opts.interconnect)

    with open(opts.out, 'w') as f:
        with open(opts.interconnect, 'r') as f2:
            for line in f2:
                if "`include" in line:
                    continue
                f.write(line)
        for file in tick_include:
            with open(os.path.join(opts.src, file), 'r') as file:
                for line in file:
                    if "`include" in line:
                        continue
                    f.write(line)

    # for file in tick_include:

        



# given the reference verilog file
# find the tick include
# put the tick include in a list (no repeats)
# find the files in the tick include
# ...

# Go into the files of the tick include
# copy the entire file
# paste into the new file