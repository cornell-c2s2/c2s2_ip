#!/bin/bash
# Converts a systemverilog file into a verilog file, also preprocessing all includes

if [ $# -lt 2 ]; then
  echo 1>&2 "$0: Missing arguments - Usage: sv2v.sh <file> <build_dir>"
  exit 2
elif [ $# -gt 2 ]; then
  echo 1>&2 "$0: Too many arguments - Usage: sv2v.sh <file> <build_dir>"
  exit 2
fi

# ANSI color codes
CYAN='\033[0;36m'
RESET='\033[0m'

# File to convert
FILE=$1
FNAME=$(basename -- "$FILE")
# Build Directory
BUILD_DIR=$2

echo -e "${CYAN}Creating file $BUILD_DIR/$FNAME${RESET}"

mkdir -p $BUILD_DIR
sv2v <(verilator -E $FILE) > $BUILD_DIR/$FNAME