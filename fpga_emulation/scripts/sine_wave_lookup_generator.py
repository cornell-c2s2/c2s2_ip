"""
Made by Will Salcedo '23
Modified by Simeon Turner '27
Automatically generates a discrete sinewave in fxp format.

Input parameters:
- BIT_WIDTH - bitwidth of sine wave fixed point
- DECIMAL_POINT - which bit is the decimal bit
- SIZE_FFT - # of points in the FFT
- output_filename - name of the output file
"""


import sys
import os
from math import sin
import math
from math import trunc
# import fxpmath

# The path where the file should be written
output_filename = sys.argv[4]
file_name = os.path.splitext(os.path.basename(output_filename))[0]

# Takes user input the bit width, decimal point, and fft size. Format command in terminal as: 
# `python sine_wave_lookup_generator.py <BIT_WIDTH> <DECIMAL_POINT> <SIZE_FFT> <output_path>`
try:
    BIT_WIDTH = int(sys.argv[1]) # 16
    DECIMAL_POINT = int(sys.argv[2]) # 8
    SIZE_FFT  = int(sys.argv[3]) # 32
except:
    print()
    sys.exit('One of your inputs was not an integer or you are missing an input.\n')


str_BIT_WIDTH = str(BIT_WIDTH) if BIT_WIDTH>9 else ('0'+str(BIT_WIDTH))
str_DECIMAL_POINT = str(DECIMAL_POINT) if DECIMAL_POINT>9 else ('0'+str(DECIMAL_POINT))
str_SIZE_FFT = str(SIZE_FFT) if SIZE_FFT>9 else ('0'+str(SIZE_FFT))

module_name_extension = 'fft_helpers_'

def write_module_header(f):
    f.write(f'`ifndef  {module_name_extension + file_name} \n')
    f.write(f'`define  {module_name_extension + file_name} \n')
    f.write('// SINE WAVE OF BIT_WIDTH = ' + str(BIT_WIDTH) + ', DECIMAL_PT =  ' + str(DECIMAL_POINT) + '\n')
    f.write('// FOR FFT OF SIZE = ' + str(SIZE_FFT) + '\n')
    f.write(f'module {module_name_extension + file_name} \n')
    f.write('   (' + '\n')
    f.write('       output logic [' + str(BIT_WIDTH) +' - 1:0] sine_wave_out [0:' + str(SIZE_FFT) + ' - 1]' + '\n')
    f.write('   );' + '\n')

with open(output_filename, 'w') as f:
    write_module_header(f)

    for n in range(SIZE_FFT):
        f.write('   assign sine_wave_out[' + str(n) + '] = ' +\
            str(round(sin( 2 * math.pi * n / SIZE_FFT) * (2**DECIMAL_POINT))) + ';\n')
    f.write('endmodule\n')
    f.write('`endif\n')

print(f'\nSine lookup generated was successful. Check for file at: {output_filename}\n')