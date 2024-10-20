#!/bin/bash
TOP_DIR=$(git rev-parse --show-toplevel)
SRC_DIR=$TOP_DIR/src

FPGA_DIR=$(pwd)

mkdir -p build

BUID_DIR=$FPGA_DIR/build

echo "Converting .v files to .sv files"

# Find all .v files in the current directory and its subdirectories
find $SRC_DIR -type f -name "*.v" | while read -r file; do
  # Get the base name of the file (without the .v extension)
  base=$(basename "${file%.v}")
  # Rename the file to have the .sv extension
  cp "$file" "$BUID_DIR/$base.sv"
  sv2v --incdir="$SRC_DIR" -w adjacent "$BUID_DIR/$base.sv"
  rm "$BUID_DIR/$base.sv"
done

echo "Conversion done"

