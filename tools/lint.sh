#!/bin/bash

RESET='\033[0m'
GREEN='\033[1;32m'

cd src
find -name *.v -not -path "./cmn/*" -exec bash -c "echo -e \"${GREEN}Checking file {}${RESET}\" && svlint {}" \;