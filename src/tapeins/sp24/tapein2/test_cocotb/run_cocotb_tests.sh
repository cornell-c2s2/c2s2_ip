#!/bin/bash

#Clean the environment
make clean_all

# Python script to extract test names from the cocotb registry
export PYTHONPATH=$PWD:$PYTHONPATH
export PYTHONPATH=$C2S2_PATH:$PYTHONPATH
MODULE="test_interconnect"

PYTHON_SCRIPT="
import inspect
import importlib
import cocotb

# Import the test module
module = importlib.import_module('$MODULE')

# Discover all cocotb tests
test_names = [
    name for name, obj in inspect.getmembers(module)
    if isinstance(obj, cocotb.regression.Test)
]

print(' '.join(test_names))
"


# Extract test names using Python
TESTS=$(python3 -c "$PYTHON_SCRIPT")

# Check if any tests were found
if [ -z "$TESTS" ]; then
    echo "No tests found in the cocotb registry."
    exit 1
fi

echo "Found tests: $TESTS"

START_TIME=$(date +%s)

#Make the logs directory
mkdir -p logs work

#Terminate all simulations after Ctrl+C
trap "echo 'Terminating...'; kill 0" SIGINT SIGTERM

# Run each test in parallel
for TEST in $TESTS; do
    (
        # Check if the test matches the naming convention {test name}_###
        if [[ "$TEST" =~ ^([a-zA-Z0-9_]+)_([0-9]{3})$ ]]; then
            TEST_NAME=${BASH_REMATCH[1]} # Extract the part before _###
            TEST_SUFFIX=${BASH_REMATCH[2]} # Extract the ### part
        else
            TEST_NAME="Misc" # For individual tests without _###
            TEST_SUFFIX=$TEST
        fi
        
        # Create a unique directory for the test
        TEST_DIR="work/$TEST_NAME/$TEST_SUFFIX"
        LOG_DIR="logs/$TEST_NAME"
        mkdir -p "$TEST_DIR" "$LOG_DIR"

        # Change to the test's unique directory
        cd "$TEST_DIR" || exit 1

        # Run the test with a unique working directory
        echo "Running test: $TEST"
        TESTCASE=$TEST TESTNAME=$TEST_NAME TESTSUFFIX=$TEST_SUFFIX make -C ../../../ > ../../../$LOG_DIR/$TEST.log 2>&1
        if [ $? -eq 0 ]; then
            echo "Test $TEST PASSED"
        else
            echo "Test $TEST FAILED"
        fi

        # Return to the original directory
        cd - >/dev/null
    ) &
done

# Wait for all background processes to complete
wait

# Record the end time
END_TIME=$(date +%s)

# Calculate the elapsed time
ELAPSED_TIME=$((END_TIME - START_TIME))

# Convert elapsed time to a human-readable format
HOURS=$((ELAPSED_TIME / 3600))
MINUTES=$(((ELAPSED_TIME % 3600) / 60))
SECONDS=$((ELAPSED_TIME % 60))

echo "All tests completed."
printf "Total runtime: %02d:%02d:%02d (HH:MM:SS)\n" $HOURS $MINUTES $SECONDS