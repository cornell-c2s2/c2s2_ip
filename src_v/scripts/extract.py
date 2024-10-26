#!/bin/bash

import re
import os
import argparse
        
def get_file_name(module_name: str):
    # lst = module_name.split('_')
    # for str in lst:
    #     if str[0].isupper():
    #         return str
    return module_name

def extract_modules(input_file, output_dir):
    # Ensure output directory exists
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    with open(input_file, 'r') as infile:
        lines = infile.readlines()

    module_content = []
    module_name = None
    inside_module = False

    for line in lines:
        # Look for the module declaration
        module_match = re.match(r'\s*module\s+(\w+)\s*\(', line)
        if module_match and not inside_module:
            module_name = module_match.group(1)  # Extract module name
            module_content = [line]  # Start capturing the module content
            inside_module = True
            continue

        # Get the file name
        file_name = get_file_name(module_name)

        # Capture lines within the module
        if inside_module:
            module_content.append(line)

        # Look for the end of the module
        if re.match(r'\s*endmodule\s*', line) and inside_module:
            # Write the module to a new file in the specified output directory
            output_file_path = os.path.join(output_dir, f'{file_name}.v')
            with open(output_file_path, 'w') as outfile:
                outfile.writelines(module_content)
            print(f'Extracted module {module_name} to {output_file_path}')
            
            # Reset for next module
            inside_module = False
            module_content = []

if __name__ == "__main__":
    # Set up argument parsing
    parser = argparse.ArgumentParser(description="Extract Verilog modules from a file and save to separate files.")
    parser.add_argument('input_file', help="Path to the input Verilog file")
    parser.add_argument('output_dir', help="Directory where extracted modules will be saved")
    
    args = parser.parse_args()

    # Call the function with arguments
    extract_modules(args.input_file, args.output_dir)
