#!/bin/bash

RESET='\033[0m'
GREEN='\033[1;32m'

find -path "./src/*" -name "*.v" -not -path "./src/cmn/*" -print0 | 
    while IFS= read -r -d '' line; do
        echo -e "${GREEN}Checking file ${line}${RESET}"
        svlint --ignore-include ${line}
    done