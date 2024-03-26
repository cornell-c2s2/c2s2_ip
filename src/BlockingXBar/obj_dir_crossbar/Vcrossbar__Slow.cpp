// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vcrossbar.h for the primary calling header

#include "Vcrossbar.h"
#include "Vcrossbar__Syms.h"

//==========

VL_CTOR_IMP(Vcrossbar) {
    Vcrossbar__Syms* __restrict vlSymsp = __VlSymsp = new Vcrossbar__Syms(this, name());
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void Vcrossbar::__Vconfigure(Vcrossbar__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

Vcrossbar::~Vcrossbar() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void Vcrossbar::_initial__TOP__1(Vcrossbar__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::_initial__TOP__1\n"); );
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->control_rdy = 1U;
}

void Vcrossbar::_eval_initial(Vcrossbar__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::_eval_initial\n"); );
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_initial__TOP__1(vlSymsp);
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
}

void Vcrossbar::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::final\n"); );
    // Variables
    Vcrossbar__Syms* __restrict vlSymsp = this->__VlSymsp;
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void Vcrossbar::_eval_settle(Vcrossbar__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::_eval_settle\n"); );
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__3(vlSymsp);
}

void Vcrossbar::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::_ctor_var_reset\n"); );
    // Body
    clk = VL_RAND_RESET_I(1);
    control = VL_RAND_RESET_Q(42);
    control_rdy = VL_RAND_RESET_I(1);
    control_val = VL_RAND_RESET_I(1);
    recv_msg = VL_RAND_RESET_Q(64);
    recv_rdy = VL_RAND_RESET_I(2);
    recv_val = VL_RAND_RESET_I(2);
    reset = VL_RAND_RESET_I(1);
    send_msg = VL_RAND_RESET_Q(64);
    send_rdy = VL_RAND_RESET_I(2);
    send_val = VL_RAND_RESET_I(2);
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT__temp_send_msg[__Vi0] = VL_RAND_RESET_I(32);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT__temp_recv_msg[__Vi0] = VL_RAND_RESET_I(32);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT__temp_send_val[__Vi0] = VL_RAND_RESET_I(1);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT__temp_recv_rdy[__Vi0] = VL_RAND_RESET_I(1);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT__temp_recv_val[__Vi0] = VL_RAND_RESET_I(1);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT__temp_send_rdy[__Vi0] = VL_RAND_RESET_I(1);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__send_rdy[__Vi0] = VL_RAND_RESET_I(1);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_val[__Vi0] = VL_RAND_RESET_I(1);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_msg[__Vi0] = VL_RAND_RESET_I(32);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT____Vcellout__crossbar_inst__recv_rdy[__Vi0] = VL_RAND_RESET_I(1);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__recv_val[__Vi0] = VL_RAND_RESET_I(1);
    }}
    { int __Vi0=0; for (; __Vi0<2; ++__Vi0) {
            crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__recv_msg[__Vi0] = VL_RAND_RESET_I(32);
    }}
    crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control = VL_RAND_RESET_Q(42);
}
