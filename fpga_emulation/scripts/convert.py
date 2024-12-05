#!/usr/bin/env python
#=========================================================================
# convert.py [options]
#=========================================================================
#
#  -h --help           Display this message
#     --vfile          The verilog file to be converted (default: src_v/build/out.v)
#     --lookup         The lookup file to be used       (default: src_v/build/sine_wave_lookup_160832.v)
#     --out            File to write extracted code     (default: src_v/fpga_converted.v)
#
# Converts the interconnect file to a format that can be used in Quartus
#
# Author : Anjelica Bian (adopted from Christopher Batten)
# Date   : Nov 17, 2024
#

import os
import re
import sys
from typing import List, Callable

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
  p.add_argument(       "--vfile",       type=str,   default=os.path.join(find_top_level(), "fpga_emulation", "build", "out.v")  )
  p.add_argument(       "--lookup",      type=str,   default=os.path.join(find_top_level(), "fpga_emulation", "build", "sine_wave_lookup_160832.v") )
  p.add_argument(       "--out",         type=str,   default=os.path.join(find_top_level(), "fpga_emulation", "fpga_converted.v") )

  opts = p.parse_args()
  if opts.help: p.error()
  return opts

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
# Parsing functions
#-------------------------------------------------------------------------

"""
Given the "begin" and "end" declarations of a block, finds all 
blocks in the content and apply the block_func to the block and 
return the modified content.
"""
def apply_block_func(content : List[str], begin : str, end : str, 
                     block_funcs : List[Callable[[List[str]], List[str]]]):
    output_content = []
    block_content = []
    inside_block = False

    for line in content:
        # Look for the module declaration
        block_match = re.match(fr'\s*{begin}\s*', line)
        if block_match and not inside_block:
            inside_block = True
            
        # Capture lines within the module
        if inside_block:
            block_content.append(line)
        else:
            output_content.append(line)

        # Look for the end of the module
        if re.match(fr'\s*{end}\s*', line) and inside_block:
            for block_func in block_funcs:
                block_content = block_func(block_content)
            output_content = output_content + block_content
            block_content = []
            inside_block = False

    return output_content

"""
Remove lines that starts at the first occurance of [begin] and ends at 
the first occurance of [end]
"""
def remove_block(content : List[str], begin : str, end : str):
    output_content = []
    inside_block = False

    for line in content:
        if begin in line:
            inside_block = True
            
        # Capture lines within the module
        if not inside_block:
            output_content.append(line)

        # Look for the end of the module
        if end in content and inside_block:
            inside_block = False

    return output_content

#------------------------------------------------------------------------
# Generate Blocks
#------------------------------------------------------------------------

"""
Cleans up generate blocks.

Given the contents of a generate block, returns content of generate 
block with 'genvar' moved to the top of the block.
"""
def clean_generate_block(content : List[str]):
    result = content

    # keeps track of a list of genvar declarations
    genvar_decl = []

    for idx in range(len(result)):
        line = result[idx]
        genvar_match = re.match(r'\s*for\s*\(genvar\s+(\w+)', line)
        
        # print(genvar_match)

        # if genvar is found, remove it from the for loop and add it to the genvar declaration list
        if genvar_match:
            # print(f"genvar found: " + genvar_match.group(1))
            line = line.replace('genvar ', '')
            genvar_decl.append(genvar_match.group(1))
            # print(f"for loop is: " + line)
        
        # update the for loop content
        result[idx] = line
    
    for genvar in genvar_decl:
        result.insert(0, "  genvar " + genvar + "; \n")

    return result

"""
Removes unnecessary genvar declarations.

Given the contents of a module, if a genvar is declared more than once,
remove all but the first declaration.

Returns the modified module content.
"""
def remove_duplicate_genvars_from_module(content : List[str]):
    result = content

    # keeps track of a list of genvar declarations indices
    genvar_dix = []

    idx = 0
    while idx < len(result):
        # print(f"idx: {idx} and len: {len(result)}")
        # for idx in range(len(result)):
        line = result[idx]
        genvar_match = re.match(r'\s*genvar\s+(\w+)', line)
        if genvar_match:
            if genvar_match.group(1) in genvar_dix:
                result.pop(idx)
            else:
                genvar_dix.append(genvar_match.group(1))
                idx += 1
        else: idx += 1

    return result

"""
Removes problems with generate statement in the module.

Given a module, moves all genvar declarations before
generate statement, and removes uncecessary generate statements.
"""
def clean_generates_from_module(content : List[str]): 
    # find all generate blocks
    output_content = content

    output_content = apply_block_func(output_content, "generate", "endgenerate", [clean_generate_block])

    output_content = apply_block_func(output_content, "module", "endmodule", [remove_duplicate_genvars_from_module])
    return output_content

"""
Add for loop names to all for loops in the content
"""
def add_for_loop_names(content : List[str]):
    result = content

    for idx in range(len(result)):
        line = result[idx]
        if ("for" in line) and ("begin" in line) and (":" not in line):
            # print(f"Found for loop #{idx}")
            line = line[:-1] + f" : for_{idx} \n"
            result[idx] = line
    
    return result

#------------------------------------------------------------------------
# Local Params
#------------------------------------------------------------------------

"""
Removes problems with localparam in the module.

Given a module, moves all localparams to the top of the module.
"""
def clean_localparams_from_module(content : List[str]):
    result = content
    param_end = []
    header_end = []

    # Is there a parameter declaration
    params_exits = re.match(r'\s*module\s+\w+\s*#\s*\(', result[0])
    
    # No parameter declaration, return
    if not params_exits:
        return result

    # Find the end of the parameter declaration
    for idx in range(len(result)):
        if re.match(r'\s*\)\s*\(', result[idx]):
            param_end.append(idx)
            break

    # check I only have one parameter declaration    
    if len(param_end) != 1:
        raise Exception("Parameter declaration not closed")
    
    # Find the end of the module header declaration
    for idx in range(len(result)):
        # end of module header declaration must succeed the end of input/output declaration
        if (re.match(r'\s*\);\s*', result[idx]) and 
            any(re.match(r'\s*input\s*', result[i]) or 
                re.match(r'\s*output\s*', result[i]) for i in range(idx))):
            header_end.append(idx)
            break

    # check I only have one module header declaration    
    if len(header_end) != 1:
        raise Exception("Module header declaration not closed")

    # Find local param declaration
    localparams = []
    for idx in range(param_end[0]):
        if re.match(r'\s*localparam\s+', result[idx]):
            localparams.append(idx)
    
    for idx in localparams[::-1]:
        if "," in result[idx]:
            comma_idx = result[idx].find(",")
            print(f"Found comma in localparam: {result[idx][:comma_idx]}")
            result.insert(header_end[0], result.pop(idx)[:comma_idx]+"; \n")
        else:
            result.insert(header_end[0], result.pop(idx)[:-1]+"; \n")

    # Parse the parameter declaration,
    # Fine the last parameter declaration
    # remove the comma
    param_idx = []
    for idx in range(param_end[0]):
        if re.match(r'\s*parameter\s+', result[idx]):
            param_idx.append(idx)
    
    if param_idx != []:
        comma_idx = result[param_idx[-1]].find(",")
        result[param_idx[-1]] = result[param_idx[-1]][:comma_idx] + " \n"

    return result

#------------------------------------------------------------------------
# SystemVerilog function calls
#------------------------------------------------------------------------

# """
# Clean $<func> statements from module by removing them
# """
# def remove_func_calls_from_module(content : List[str], func_name : str):
#     result = content

#     for idx in range(len(result)):
#         line = result[idx]
#         func_call = re.match(fr'\s*\${func_name}\s*', line)
#         if func_call:
#             result.pop(idx)
    
#     return result

"""
Replaces [fft_helpers_SineWave] with [sine_wave_lookup] in any content.
If [fft_helpers_SineWave] does not exist, return the content as is.

The function reads the lookup file and replaces the sine calls with the
sine_wave_lookup calls

This function DOES NOT remove the [fft_helpers_SineWave] module declaration
"""
def replace_sine_with_lookup(content : List[str], lookup_file : str):
    inside_block = False
    result = []

    # Read the lookup file
    with open(lookup_file, "r") as file:
        lookup_content = file.readlines()

    # Get the name of the lookup table
    lookup_module_name = re.match(r'\s*`ifndef\s+(\w+)', lookup_content[0]).group(1)

    for line in content:
        module_start = re.match(r'(\s*)fft_helpers_SineWave #\(\s*', line)
        module_end = re.match(r'\s*\);\s*', line)
        if module_start:
            # Find number of spaces before the module declaration (aka tab size)
            tab = module_start.group(1)
            inside_block = True

        if not inside_block:
            result.append(line)
        
        if module_end and inside_block:
            inside_block = False
            result.append(f"{tab + lookup_module_name} sine_wave ( \n")
            result.append(f"{tab * 2}.sine_wave_out (sine_wave_out) \n")
            result.append(f"{tab}); \n")

    return result

"""
Cleans the entire interconnect file with function calls

Given the entire interconnect file, replace all instances of
[fft_helpers_SineWave] with [sine_wave_lookup],
removes fft_helpers_SineWave declaration, and
removes all function calls [$pow]
removes all function calls [$error]. 
Return the modified content
"""
def clean_function_from_all(content : List[str], lookup_file : str):
    result = []
    inside_block = False

    # Mark the begin and end of fft_helpers_SineWave 
    begin = "ifndef fft_helpers_SINE_WAVE"
    end = "endif"

    found_end = False

    for i in range(len(content)):
        line = content[i]
        if begin in line:
            inside_block = True
            
        # Capture lines within the module
        if not (inside_block or ("$error" in line) or found_end):
            result.append(line)
        
        found_end = False
        
        if ("$error" in line and 
            re.match(r"\s*if.*begin\s*$", content[i-1]) and
            re.match(r"\s*end\s*$", content[i+1])):
            if result[-1] == content[i-1]:
                result.pop()
            found_end = True

        # Look for the end of the module
        if (end in line) and inside_block:
            inside_block = False
    
    with open(lookup_file, "r") as file:
        lookup_content = file.readlines()

    result = result + lookup_content

    # output_content = remove_func_calls_from_module(output_content, func_name)

    return result

"""
Removes all unsed declarations from the module

comments out every line that starts with `logic unused` or `wire unused`
"""
def remove_unused_declarations(content : List[str]):
    result = content

    content_ok = True
    for idx in range(len(result)):
        line = result[idx]
        if re.match(r'\s*logic\s+unused\w*\s*=', line) or re.match(r'\s*wire\s+unused\w*\s*=', line):
            content_ok = False
        if (not content_ok):
            result[idx] = "// " + line
        # End of the declaration
        if (not content_ok) and ";" in line:
            content_ok = True
    
    return result

#------------------------------------------------------------------------
# Piece everything together
#------------------------------------------------------------------------

"""
Returns a copy of module content with everything cleaned up
"""
def extract_module(content : List[str], lookup_file : str):
    output_content = content

    output_content = apply_block_func(output_content, "module", "endmodule", [clean_localparams_from_module])
    output_content = apply_block_func(output_content, "module", "endmodule", [clean_generates_from_module])
    output_content = add_for_loop_names(output_content)
    output_content = clean_function_from_all(output_content, lookup_file)
    output_content = replace_sine_with_lookup(output_content, lookup_file)
    output_content = remove_unused_declarations(output_content)

    return output_content

#-------------------------------------------------------------------------
# Main
#-------------------------------------------------------------------------

if __name__ == "__main__":
    opts = parse_cmdline()

    # Open the file
    with open(opts.vfile, "r") as file:
        content = file.readlines()

    new_content = extract_module(content, opts.lookup)

    # Write the modified content to a new file
    with open(opts.out, "w") as file:
        for line in new_content:
            file.write(line)

    print(f'Conversion was successful. Check for file at: {opts.out}\n')
