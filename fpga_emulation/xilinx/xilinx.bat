@echo off

set CONVERT=0
set COMPILE=0
set PROGRAM=0
set CLEAN=0
set ARG_PASS=0

IF "%1"=="convert" (
    set CONVERT=1
    set ARG_PASS=1
) 
IF "%1"=="compile" (
    set COMPILE=1
    set ARG_PASS=1
) 
IF "%1"=="program" (
    set PROGRAM=1
    set ARG_PASS=1
) 
IF "%1"=="setup" (
    set COMPILE=1
    set PROGRAM=1
    set ARG_PASS=1
) 
IF "%1"=="all" (
    set CONVERT=1
    set COMPILE=1
    set PROGRAM=1
    set ARG_PASS=1
) 
IF "%1"=="clean" (
    set CLEAN=1
    set ARG_PASS=1
)
IF %ARG_PASS%==0 (
    echo Error: missing an argument. Aborting.
    exit /b 1
)

for /f "delims=" %%i in ('git rev-parse --show-toplevel') do set TOP_DIR=%%i
set SRC_DIR=%TOP_DIR%\src
set XILINX_DIR=%TOP_DIR%\fpga_emulation\xilinx
set BUILD_DIR=%XILINX_DIR%\build
set SCRIPT_DIR=%TOP_DIR%\fpga_emulation\scripts

rem CONVERSION
set src_emulation_dir=%SRC_DIR%\tapeins\sp24\fpga_emulation2
set interconnect_file=%src_emulation_dir%\interconnect_fpga.v

set pickled_file=%BUILD_DIR%\Interconnect_Fpga_pickled.sv
set lookup_file=%BUILD_DIR%\sine_wave_lookup_16_8_32.sv

rem Quartus Programming
set PATH=C:\intelFPGA_lite\23.1std\quartus\bin64\;%PATH%
set PROJECT_NAME=emulation_sp24_tapein2
set TCL_SCRIPT=emulation_sp24_tapein2.tcl
set SOF_FILE=output_files\emulation_sp24_tapein2.sof
set CABLE_INDEX=1

IF %CONVERT% == 1 (

  mkdir "%BUILD_DIR%"
  python %SCRIPT_DIR%\sine_wave_lookup_generator.py 16 8 32 %lookup_file%
  python %SCRIPT_DIR%\pickle.py --src %SRC_DIR% --interconnect %interconnect_file% --out %pickled_file%
  python %SCRIPT_DIR%\convert_xilinx.py --vfile %pickled_file% --lookup %lookup_file% --out %XILINX_DIR%\interconnect_fpga.sv

)

IF %CLEAN% == 1 (

  del "%XILINX_DIR%\interconnect_fpga.sv"
  rmdir /s /q "%XILINX_DIR%\build"

)