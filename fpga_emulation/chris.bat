@echo off

rem File that converts all files to Quartus compatible, compiles the program, and programs
rem the FPGA, all without the need of the Quartus GUI. Also cleans up all generated files if needed.

rem Summary of commands:
rem `convert` - converts all Verilog files used in the design to Quartus compatible
rem `compile` - compiles the current project
rem `program` - programs the current project onto the FPGA
rem `setup`   - compiles and programs the current project onto the FPGA. Helpful if no conversion necessary.
rem `all`     - executes conversion, compilation, and programming (performs all generation actions)
rem `clean`   - deletes all files created from conversion, project creation, and compilation

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
set FPGA_DIR=%TOP_DIR%\fpga_emulation
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
IF %CONVERT% == 1 (
    echo:
    echo Converting tapein files.
    echo:

    mkdir "%BUILD_DIR%"
    python %SCRIPT_DIR%\sine_wave_lookup_generator.py 16 8 32 %lookup_file%
    python %SCRIPT_DIR%\pickel.py --src %SRC_DIR% --interconnect %interconnect_file% --out %pickled_file%
    python %SCRIPT_DIR%\convert.py --vfile %pickled_file% --lookup %lookup_file% --out %FPGA_DIR%\interconnect_fpga.v

    echo:
    echo File converted successfully.
    echo:
)


rem 2: Execute the TCL script through quartus_sh
IF %COMPILE% == 1 (
    echo:
    echo Executing TCL script: %TCL_SCRIPT%
    echo:

    C:\intelFPGA_lite\23.1std\quartus\bin64\quartus_sh -t %TCL_SCRIPT%

    if %ERRORLEVEL% neq 0 (
        echo Error running TCL script. Aborting.
        exit /b 1
    )

    echo:
    echo TCL script executed successfully.
    echo:
)


rem 3: Program the FPGA with quartus_pgm
IF %PROGRAM% == 1 (
    echo:
    echo Programming FPGA with SOF file: %SOF_FILE%
    echo:

    C:\intelFPGA_lite\23.1std\quartus\bin64\quartus_pgm -m JTAG -o "p;%SOF_FILE%@%CABLE_INDEX%"

    if %ERRORLEVEL% neq 0 (
        echo Error programming FPGA. Aborting.
        exit /b 1
    )

    echo:
    echo FPGA programming completed successfully.
    echo:
)

rem 4: Completely clear out all generated files
IF %CLEAN% == 1 (
    del "%FPGA_DIR%\interconnect_fpga.v"
    del "%FPGA_DIR%\*.qpf"
    del "%FPGA_DIR%\*.qsf"
    del "%FPGA_DIR%\*.qws"
    del "%FPGA_DIR%\*.bak"
    rmdir /s /q "%FPGA_DIR%\build"
    rmdir /s /q "%FPGA_DIR%\db"
    rmdir /s /q "%FPGA_DIR%\incremental_db"
    rmdir /s /q "%FPGA_DIR%\log"
    rmdir /s /q "%FPGA_DIR%\output_files"
)
