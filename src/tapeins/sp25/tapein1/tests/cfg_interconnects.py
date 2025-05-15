# ===================================================================
# Author: Johnny Martinez, Tean Lai
# Date: 05/14/2025
# 
# Spec: Contains python classes for each routing element in the SP25 
# Tapein1 top level RTL. Each class contains the configuration bits
# for an i/o of a given routing structure. 
# Ex:
#   InXbarCfg.ROUTER_ARBITER is the configuration message that is 
#   sent to the input crossbar go select the input as the ROUTER 
#   and output as the Arbiter (i.e. loopback).
# ===================================================================


class InXbarCfg:
    """
    Represents the message to send to the input crossbar to configure it. For
    example, sending in 0b1010 will configure it to input from router and output
    to arbiter.

    TODO: Need to add rest of config messages. Tean's note: not sure if it might
    be better to have a function to generate the message, since
    """
    ROUTER_ARBITER = 0b1010
    ROUTER_FFT1 = 0b1000
    ROUTER_FFT2 = 0b1001
    LFSR_FFT1 = 0b0000
    LFSR_FFT2 = 0b0001
    FIFO_ARBITER = 0b0110
    FIFO_FFT1 = 0b0100
    FIFO_FFT2 = 0b0101

class ClsXbarCfg:
    """
    Serves a similar purpose as InXbarCfg, but for the classifier crossbar
    """
    ROUTER_CLS     = 0b1001
    ROUTER_ARBITER = 0b1010
    FFT1_ARBITER   = 0b0010
    FFT2_ARBITER   = 0b0110
    FFT1_CLS       = 0b0001
    FFT2_CLS       = 0b0101
    FFT1_MISR      = 0b0000
    FFT2_MISR      = 0b0100

class OutXbarCfg:
    """
    Serves a similar purpose as InXbarCfg and ClsXbarCfg, but for the output
    crossbar.

    This should correspond with the Output  addressing scheme in the RTL.
    """
    CLS_ARBITER    = 0b000
    ROUTER_ARBITER = 0b010


class RouterOut:
    """
    The router has several outputs to different blocks. These enums represent
    which output they are to the router. This is intended to be used as the 
    address bits for the SPI packet sent to the router. 

    This should correspond with the Router addressing scheme in the RTL.
    """
    LBIST_CTRL             = 0b0000
    IN_XBAR                = 0b0001
    IN_XBAR_CTRL           = 0b0010
    CLS_XBAR               = 0b0011
    CLS_XBAR_CTRL          = 0b0100
    CLS_CUT_FREQ_CTRL      = 0b0101
    CLS_MAG_CTRL           = 0b0110
    CLS_SAMP_FREQ_CTRL     = 0b0111
    OUT_XBAR               = 0b1000
    OUT_XBAR_CTRL          = 0b1001
    ARBITER                = 0b1010


class ArbiterIn:
    """
    The arbiter has several inputs from different blocks. These enums represent
    which input they are to the arbiter. This is intended to be used as the
    address bits for the SPI packet sent to the arbiter.

    This should correspond with the Arbiter addressing scheme in the RTL.
    """
    ROUTER     = 0
    IN_XBAR    = 1
    CLS_XBAR   = 2
    OUT_XBAR   = 3
    LBIST_CTRL = 4