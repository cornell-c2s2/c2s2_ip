#!/bin/bash

import os
import re
import sys
from typing import List

# scan through the file and look for delimiter module and endmodule

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
        
        print(genvar_match)

        # if genvar is found, remove it from the for loop and add it to the genvar declaration list
        if genvar_match:
            print(f"genvar found: " + genvar_match.group(1))
            line = line.replace('genvar ', '')
            genvar_decl.append(genvar_match.group(1))
            print(f"for loop is: " + line)
        
        # update the for loop content
        result[idx] = line
    
    for genvar in genvar_decl:
        result.insert(0, "  genvar " + genvar + ";")

    return result

"""
Removes unnecessary genvar declarations.

Given the contents of a module, if a genvar is declared more than once,
remove all but the first declaration.

Returns the modified module content.
"""
def remove_duplicate_genvars(content : List[str]):
    result = content

    # keeps track of a list of genvar declarations indices
    genvar_dix = []

    idx = 0
    while idx < len(result):
        print(f"idx: {idx} and len: {len(result)}")
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
Moves localparams outside parameter declaration.

Given a module, moves all localparams to the top of the module.
"""
def move_localparams(content : List[str]):
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
        print(re.match(r'\s*\);\s*', result[idx]))
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
    
    for idx in localparams:
        result.insert(header_end[0], result.pop(idx))

    return result

def extract_module(content : List[str]):
    module_content = []
    inside_module = False

    for line in content:
        # print(line)
        # Look for the module declaration
        module_match = re.match(r'\s*module\s+', line)
        if module_match and not inside_module:
            # print(f"found module: {line}")
            module_content = [line]  # Start capturing the module content
            inside_module = True
            continue

        # Capture lines within the module
        if inside_module:
            module_content.append(line)
            # print(line)

        # Look for the end of the module
        if re.match(r'\s*endmodule\s*', line) and inside_module:
            return module_content

    return None

def main():
    filename = sys.argv[1]
    # Open the file
    with open(filename, "r") as file:
        content = file.readlines()

    # Extract the module content
    module_content = extract_module(content)

    # Clean up generate blocks
    module_content = clean_generate_block(module_content)

    # Remove duplicate genvars
    module_content = remove_duplicate_genvars(module_content)

    # Move localparams outside parameter declaration
    module_content = move_localparams(module_content)

    # Write the modified content to a new file
    with open("src_v/rtl/arbiter_clean.sv", "w") as file:
        for line in module_content:
            file.write(line)