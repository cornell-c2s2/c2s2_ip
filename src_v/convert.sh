#!/bin/bash

# Find all .v files in the current directory and its subdirectories
find . -type f -name "*.v" | while read -r file; do
  # Get the base name of the file (without the .v extension)
  base="${file%.v}"
  echo $base
  # Rename the file to have the .sv extension
  mv "$file" "$base.sv"
  sv2v --incdir="$(pwd)" -w adjacent "$base.sv"
  rm "$base.sv"
done