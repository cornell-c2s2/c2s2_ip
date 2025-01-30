# this clears previous blocks and proofs
clear -all 

# this says to initiate coverage checking, and allows you to list the modes (can also be done in gui)
check_cov -init -type all -model {branch toggle statement} -toggle_ports_only

# you must analyze all the files in your design (source and testbench) before doing anything in jasper
analyze -sv spi/helpers/minion_adapter.v spi/tests/minion_adapter_sva.sv

# specify the top level module, in this case the testbench 
elaborate -top spi_helpers_Minion_Adapter -create_related_covers {precondition witness}

# specify clock and reset signals
clock clk
reset reset

prove -bg -task {<embedded>}
check_cov -measure -type {coi proof bound}