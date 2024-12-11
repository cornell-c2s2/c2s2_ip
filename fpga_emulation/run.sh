#~/intelFPGA_lite/23.1std/quartus/bin/quartus_sh -t emulation_sp24_tapein2.tcl

~/intelFPGA_lite/23.1std/quartus/bin/quartus_pgm -m JTAG -o "p;output_files/emulation_sp24_tapein2.sof@1"
#~/intelFPGA_lite/23.1std/quartus/bin/quartus_pgm -m AS -o "p;output_files/output_file.pof"

echo "DONE"