@echo off
for /f "delims=" %%i in ('git rev-parse --show-toplevel') do set TOP_DIR=%%i
set SRC_DIR=%TOP_DIR%\src
set FPGA_DIR=%PWD%
set BUILD_DIR=%FPGA_DIR%\build
set SCRIPT_DIR=%FPGA_DIR%\scripts

rem CONVERSION
set src_emulation_dir=%SRC_DIR%\tapeins\sp24\fpga_emulation2
set interconnect_file=%src_emulation_dir%\interconnect_fpga.v

set pickled_file=%BUILD_DIR%\Interconnect_Fpga_pickled.v
set lookup_file=%BUILD_DIR%\sine_wave_lookup_16_8_32.v

rem Quartus Programming
set PATH=C:\intelFPGA_lite\23.1std\quartus\bin64\;%PATH%
set PROJECT_NAME=emulation_sp24_tapein2
set TCL_SCRIPT=emulation_sp24_tapein2.tcl
set SOF_FILE=output_files\emulation_sp24_tapein2.sof
set CABLE_INDEX=1

rem 1. Convert
mkdir -p %BUILD_DIR%
python %SCRIPT_DIR%\sine_wave_lookup_generator.py 16 8 32 %lookup_file%
python %SCRIPT_DIR%\pickel.py --src %SRC_DIR% --interconnect %interconnect_file% --out %pickled_file%
python %SCRIPT_DIR%\convert.py --vfile %pickled_file% --lookup %lookup_file% --out %FPGA_DIR%\interconnect_fpga.v

echo File Converted Successfully


rem 2: Execute the TCL script through quartus_sh
echo Running TCL script: %TCL_SCRIPT%
C:\intelFPGA_lite\23.1std\quartus\bin64\quartus_sh -t %TCL_SCRIPT%
if %ERRORLEVEL% neq 0 (
    echo Error running TCL script. Aborting.
    exit /b 1
)

rem 3: Program the FPGA with quartus_pgm
echo Programming FPGA with SOF file: %SOF_FILE%
C:\intelFPGA_lite\23.1std\quartus\bin64\quartus_pgm -m JTAG -o "p;%SOF_FILE%@%CABLE_INDEX%"
if %ERRORLEVEL% neq 0 (
    echo Error programming FPGA. Aborting.
    exit /b 1
)
echo FPGA programming completed successfully.