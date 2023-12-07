#!/bin/bash

RESET='\033[0m'
GREEN='\033[1;32m'
RED='\033[1;31m'

mkdir build -p

# Flag to track if there are any errors
has_errors=false

for d in ./src/*/ ; do
  echo -e "${GREEN}Checking IP ${d}${RESET}"
  pytest "$@" --suppress-no-test-exit-code $d

  # Check the exit code of pytest
  if [ $? -ne 0 ]; then
      echo -e "${RED}Pytest error(s) found in $d${RESET}"
      has_errors=true
  fi
done


# Check if there were any errors
if [ "$has_errors" = true ]; then
    echo -e "${RED}One or more files have errors.${RESET}"
    exit 1
else
    echo -e "${GREEN}All files passed pytest checks.${RESET}"
    exit 0
fi

rm build/tmp.out
