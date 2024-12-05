TOP_DIR=$(git rev-parse --show-toplevel)

FPGA_DIR=$TOP_DIR/src_v
TEMP_DIR=$FPGA_DIR/temp

find $FPGA_DIR -type f -name "*.v" | while read -r file; do
  rm "$file"
done

find $TEMP_DIR -type f -name "*.v" | while read -r file; do
  rm "$file"
done