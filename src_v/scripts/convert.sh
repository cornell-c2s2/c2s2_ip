#!/bin/bash
TOP_DIR=$(git rev-parse --show-toplevel)
SRC_DIR=$TOP_DIR/src

FPGA_DIR=$TOP_DIR/src_v

mkdir -p temp

TEMP_DIR=$FPGA_DIR/temp

echo "Converting .v files to .sv files"

# Find all .v files in the current directory and its subdirectories
find $SRC_DIR -type f -name "*.v" | while read -r file; do
  # Get the base name of the file (without the .v extension)
  base=$(basename "${file%.v}")
  # Rename the file to have the .sv extension
  cp "$file" "$TEMP_DIR/$base.sv"
  sv2v --incdir="$SRC_DIR" -w adjacent "$TEMP_DIR/$base.sv"
  rm "$TEMP_DIR/$base.sv"
done

echo "Conversion done"

