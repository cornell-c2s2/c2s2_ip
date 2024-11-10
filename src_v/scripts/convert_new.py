#!/usr/bin/bash

import os
import re
import sys
from typing import List, Callable

# scan through the file and look for delimiter module and endmodule

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
def remove_duplicate_genvars(content : List[str]):
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
def clean_generates(content : List[str]): 
    # find all generate blocks
    output_content = content

    output_content = apply_block_func(output_content, "generate", "endgenerate", [clean_generate_block])

    output_content = apply_block_func(output_content, "module", "endmodule", [remove_duplicate_genvars])
    return output_content

"""
Removes problems with localparam in the module.

Given a module, moves all localparams to the top of the module.
"""
def clean_localparams(content : List[str]):
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
        # print(re.match(r'\s*\);\s*', result[idx]))
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

"""
Returns a copy of module content with everything cleaned up
"""
def extract_module(content : List[str]):
    output_content = content

    output_content = apply_block_func(output_content, "module", "endmodule", [clean_localparams])
    output_content = apply_block_func(output_content, "module", "endmodule", [clean_generates])

    return output_content

if __name__ == "__main__":
    filename = sys.argv[1]
    print("hello")
    print(filename)
    # Open the file
    with open(filename, "r") as file:
        content = file.readlines()

    new_content = extract_module(content)

    # print(new_content)

    # Write the modified content to a new file
    with open("/home/yb265/c2s2/c2s2_ip/src_v/interconnect_convered_fpga.v", "w") as file:
        for line in new_content:
            file.write(line)
