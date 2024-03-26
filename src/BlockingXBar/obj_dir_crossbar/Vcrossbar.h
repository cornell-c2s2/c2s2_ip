// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef _VCROSSBAR_H_
#define _VCROSSBAR_H_  // guard

#include "verilated.h"

//==========

class Vcrossbar__Syms;

//----------

VL_MODULE(Vcrossbar) {
  public:
    
    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(clk,0,0);
    VL_OUT8(control_rdy,0,0);
    VL_IN8(control_val,0,0);
    VL_OUT8(recv_rdy,1,0);
    VL_IN8(recv_val,1,0);
    VL_IN8(reset,0,0);
    VL_IN8(send_rdy,1,0);
    VL_OUT8(send_val,1,0);
    VL_IN64(control,41,0);
    VL_IN64(recv_msg,63,0);
    VL_OUT64(send_msg,63,0);
    
    // LOCAL SIGNALS
    // Internals; generally not touched by application code
    QData/*41:0*/ crossbar__DOT__v__DOT__crossbar_inst__DOT__stored_control;
    IData/*31:0*/ crossbar__DOT__v__DOT__temp_send_msg[2];
    IData/*31:0*/ crossbar__DOT__v__DOT__temp_recv_msg[2];
    CData/*0:0*/ crossbar__DOT__v__DOT__temp_send_val[2];
    CData/*0:0*/ crossbar__DOT__v__DOT__temp_recv_rdy[2];
    CData/*0:0*/ crossbar__DOT__v__DOT__temp_recv_val[2];
    CData/*0:0*/ crossbar__DOT__v__DOT__temp_send_rdy[2];
    
    // LOCAL VARIABLES
    // Internals; generally not touched by application code
    CData/*0:0*/ __Vclklast__TOP__clk;
    CData/*0:0*/ crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__send_rdy[2];
    CData/*0:0*/ crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_val[2];
    IData/*31:0*/ crossbar__DOT__v__DOT____Vcellout__crossbar_inst__send_msg[2];
    CData/*0:0*/ crossbar__DOT__v__DOT____Vcellout__crossbar_inst__recv_rdy[2];
    CData/*0:0*/ crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__recv_val[2];
    IData/*31:0*/ crossbar__DOT__v__DOT____Vcellinp__crossbar_inst__recv_msg[2];
    
    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    Vcrossbar__Syms* __VlSymsp;  // Symbol table
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(Vcrossbar);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// The special name  may be used to make a wrapper with a
    /// single model invisible with respect to DPI scope names.
    Vcrossbar(const char* name = "TOP");
    /// Destroy the model; called (often implicitly) by application code
    ~Vcrossbar();
    
    // API METHODS
    /// Evaluate the model.  Application must call when inputs change.
    void eval() { eval_step(); }
    /// Evaluate when calling multiple units/models per time step.
    void eval_step();
    /// Evaluate at end of a timestep for tracing, when using eval_step().
    /// Application must call after all eval() and before time changes.
    void eval_end_step() {}
    /// Simulation complete, run final blocks.  Application must call on completion.
    void final();
    
    // INTERNAL METHODS
  private:
    static void _eval_initial_loop(Vcrossbar__Syms* __restrict vlSymsp);
  public:
    void __Vconfigure(Vcrossbar__Syms* symsp, bool first);
  private:
    static QData _change_request(Vcrossbar__Syms* __restrict vlSymsp);
    static QData _change_request_1(Vcrossbar__Syms* __restrict vlSymsp);
  public:
    static void _combo__TOP__3(Vcrossbar__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset() VL_ATTR_COLD;
  public:
    static void _eval(Vcrossbar__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(Vcrossbar__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(Vcrossbar__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _initial__TOP__1(Vcrossbar__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _sequent__TOP__2(Vcrossbar__Syms* __restrict vlSymsp);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
