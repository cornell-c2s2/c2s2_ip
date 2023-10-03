#!/bin/bash

RESET='\033[0m'
GREEN='\033[1;32m'
RED='\033[1;31m'

mkdir build -p

# Flag to track if there are any errors
has_errors=false
 
while IFS= read -r -d '' line; do
    echo -e "${GREEN}Checking file ${line}${RESET}"
    svlint "${line}" --github-actions

    # Check the exit code of svlint
    if [ $? -ne 0 ]; then
        echo -e "${RED}Linting error(s) found in $line${RESET}"
        has_errors=true
    fi

    verilator "${line}" --lint-only -Wall -Wno-DECLFILENAME -Wno-MULTITOP \
        |& tee /dev/stderr \
        | ifne false

    # Check the exit code of verilator
    if [ $? -ne 0 ]; then
        echo -e "${RED}Verilog compilation error(s) found in $line${RESET}"
        has_errors=true
    fi
done < <(find "./src" -name "*.v" -not -path "./src/cmn/*" -print0)


# Check if there were any errors
if [ "$has_errors" = true ]; then
    echo -e "${RED}One or more files have errors.${RESET}"
    exit 1
else
    echo -e "${GREEN}All files passed svlint checks.${RESET}"
    exit 0
fi

rm build/tmp.out
