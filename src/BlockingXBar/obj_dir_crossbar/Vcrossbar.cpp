// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vcrossbar.h for the primary calling header

#include "Vcrossbar.h"
#include "Vcrossbar__Syms.h"

//==========

void Vcrossbar::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vcrossbar::eval\n"); );
    Vcrossbar__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
#ifdef VL_DEBUG
    // Debug assertions
    _eval_debug_assertions();
#endif  // VL_DEBUG
    // Initialize
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) _eval_initial_loop(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Clock loop\n"););
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("crossbarTestHarnessVRTL.v", 100, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void Vcrossbar::_eval_initial_loop(Vcrossbar__Syms* __restrict vlSymsp) {
    vlSymsp->__Vm_didInit = true;
    _eval_initial(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        _eval_settle(vlSymsp);
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("crossbarTestHarnessVRTL.v", 100, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void Vcrossbar::_sequent__TOP__2(Vcrossbar__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::_sequent__TOP__2\n"); );
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if (vlTOPp->reset) {
        vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control = 0ULL;
    } else {
        if (vlTOPp->control_val) {
            vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                = vlTOPp->control;
        }
    }
}

VL_INLINE_OPT void Vcrossbar::_combo__TOP__3(Vcrossbar__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::_combo__TOP__3\n"); );
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->crossbar__DOT__v__DOT__temp_recv_val[0U] 
        = (1U & (IData)(vlTOPp->recv_val));
    vlTOPp->crossbar__DOT__v__DOT__temp_recv_val[1U] 
        = (1U & ((IData)(vlTOPp->recv_val) >> 1U));
    vlTOPp->crossbar__DOT__v__DOT__temp_send_rdy[0U] 
        = (1U & (IData)(vlTOPp->send_rdy));
    vlTOPp->crossbar__DOT__v__DOT__temp_send_rdy[1U] 
        = (1U & ((IData)(vlTOPp->send_rdy) >> 1U));
    vlTOPp->crossbar__DOT__v__DOT__temp_recv_msg[0U] 
        = (IData)(vlTOPp->recv_msg);
    vlTOPp->crossbar__DOT__v__DOT__temp_recv_msg[1U] 
        = (IData)((vlTOPp->recv_msg >> 0x20U));
    vlTOPp->crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__recv_val[0U] 
        = vlTOPp->crossbar__DOT__v__DOT__temp_recv_val
        [1U];
    vlTOPp->crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__recv_val[1U] 
        = vlTOPp->crossbar__DOT__v__DOT__temp_recv_val
        [0U];
    vlTOPp->crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__send_rdy[0U] 
        = vlTOPp->crossbar__DOT__v__DOT__temp_send_rdy
        [1U];
    vlTOPp->crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__send_rdy[1U] 
        = vlTOPp->crossbar__DOT__v__DOT__temp_send_rdy
        [0U];
    vlTOPp->crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__recv_msg[0U] 
        = vlTOPp->crossbar__DOT__v__DOT__temp_recv_msg
        [1U];
    vlTOPp->crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__recv_msg[1U] 
        = vlTOPp->crossbar__DOT__v__DOT__temp_recv_msg
        [0U];
    vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_val[(1U 
                                                                        & (IData)(
                                                                                (vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                                                                                >> 0x28U)))] 
        = vlTOPp->crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__recv_val
        [(1U & (IData)((vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                        >> 0x29U)))];
    if ((1U & (IData)((vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                       >> 0x28U)))) {
        vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_val[0U] = 0U;
    }
    if ((1U & (~ (IData)((vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                          >> 0x28U))))) {
        vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_val[1U] = 0U;
    }
    vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__recv_rdy[(1U 
                                                                        & (IData)(
                                                                                (vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                                                                                >> 0x29U)))] 
        = vlTOPp->crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__send_rdy
        [(1U & (IData)((vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                        >> 0x28U)))];
    if ((1U & (IData)((vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                       >> 0x29U)))) {
        vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__recv_rdy[0U] = 0U;
    }
    if ((1U & (~ (IData)((vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                          >> 0x29U))))) {
        vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__recv_rdy[1U] = 0U;
    }
    vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_msg[(1U 
                                                                        & (IData)(
                                                                                (vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                                                                                >> 0x28U)))] 
        = vlTOPp->crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__recv_msg
        [(1U & (IData)((vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                        >> 0x29U)))];
    if ((1U & (IData)((vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                       >> 0x28U)))) {
        vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_msg[0U] = 0U;
    }
    if ((1U & (~ (IData)((vlTOPp->crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control 
                          >> 0x28U))))) {
        vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_msg[1U] = 0U;
    }
    vlTOPp->crossbar__DOT__v__DOT__temp_send_val[1U] 
        = vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_val
        [0U];
    vlTOPp->crossbar__DOT__v__DOT__temp_send_val[0U] 
        = vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_val
        [1U];
    vlTOPp->crossbar__DOT__v__DOT__temp_recv_rdy[1U] 
        = vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__recv_rdy
        [0U];
    vlTOPp->crossbar__DOT__v__DOT__temp_recv_rdy[0U] 
        = vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__recv_rdy
        [1U];
    vlTOPp->crossbar__DOT__v__DOT__temp_send_msg[1U] 
        = vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_msg
        [0U];
    vlTOPp->crossbar__DOT__v__DOT__temp_send_msg[0U] 
        = vlTOPp->crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_msg
        [1U];
    vlTOPp->send_val = ((2U & (IData)(vlTOPp->send_val)) 
                        | vlTOPp->crossbar__DOT__v__DOT__temp_send_val
                        [0U]);
    vlTOPp->send_val = ((1U & (IData)(vlTOPp->send_val)) 
                        | (vlTOPp->crossbar__DOT__v__DOT__temp_send_val
                           [1U] << 1U));
    vlTOPp->recv_rdy = ((2U & (IData)(vlTOPp->recv_rdy)) 
                        | vlTOPp->crossbar__DOT__v__DOT__temp_recv_rdy
                        [0U]);
    vlTOPp->recv_rdy = ((1U & (IData)(vlTOPp->recv_rdy)) 
                        | (vlTOPp->crossbar__DOT__v__DOT__temp_recv_rdy
                           [1U] << 1U));
    vlTOPp->send_msg = ((0xffffffff00000000ULL & vlTOPp->send_msg) 
                        | (IData)((IData)(vlTOPp->crossbar__DOT__v__DOT__temp_send_msg
                                          [0U])));
    vlTOPp->send_msg = ((0xffffffffULL & vlTOPp->send_msg) 
                        | ((QData)((IData)(vlTOPp->crossbar__DOT__v__DOT__temp_send_msg
                                           [1U])) << 0x20U));
}

void Vcrossbar::_eval(Vcrossbar__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::_eval\n"); );
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if (((IData)(vlTOPp->clk) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk)))) {
        vlTOPp->_sequent__TOP__2(vlSymsp);
    }
    vlTOPp->_combo__TOP__3(vlSymsp);
    // Final
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
}

VL_INLINE_OPT QData Vcrossbar::_change_request(Vcrossbar__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::_change_request\n"); );
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData Vcrossbar::_change_request_1(Vcrossbar__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::_change_request_1\n"); );
    Vcrossbar* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void Vcrossbar::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vcrossbar::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((control & 0ULL))) {
        Verilated::overWidthError("control");}
    if (VL_UNLIKELY((control_val & 0xfeU))) {
        Verilated::overWidthError("control_val");}
    if (VL_UNLIKELY((recv_val & 0xfcU))) {
        Verilated::overWidthError("recv_val");}
    if (VL_UNLIKELY((reset & 0xfeU))) {
        Verilated::overWidthError("reset");}
    if (VL_UNLIKELY((send_rdy & 0xfcU))) {
        Verilated::overWidthError("send_rdy");}
}
#endif  // VL_DEBUG
