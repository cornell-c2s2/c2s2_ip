import math

def crossbar_2d_func_model(recv_msg, recv_val, send_rdy, control, n_inputs, n_outputs, entries):
    """
    Functional model for crossbar_2d
    
    Args:
        recv_msg: List of lists: recv_msg[N_INPUTS][ENTRIES]
        recv_val: List of N_INPUTS integers (0/1)
        send_rdy: List of N_OUTPUTS integers (0/1)
        control: Integer value of control
        n_inputs: Number of inputs
        n_outputs: Number of outputs
        entries: Number of entries per input/output port
        
    Returns:
        send_msg, send_val, recv_rdy
    """
    input_sel_bits = math.ceil(math.log2(n_inputs))
    output_sel_bits = math.ceil(math.log2(n_outputs))
    
    # Extract input_sel and output_sel from control
    # input_sel is in the upper bits
    input_sel = (control >> output_sel_bits) & ((1 << input_sel_bits) - 1)
    # output_sel is in the lower bits
    output_sel = control & ((1 << output_sel_bits) - 1)
    
    # Ensure input_sel and output_sel are valid indices
    input_sel = min(input_sel, n_inputs - 1)
    output_sel = min(output_sel, n_outputs - 1)
    
    # Initialize arrays
    send_msg = [[0] * entries for _ in range(n_outputs)]
    send_val = [0] * n_outputs
    recv_rdy = [0] * n_inputs
    
    # comb
    for i in range(n_outputs):
        if i != output_sel:
            # Not selected output - set to 0
            send_msg[i] = [0] * entries
            send_val[i] = 0
        else:
            # Selected output - connect to selected input
            send_msg[i] = list(recv_msg[input_sel])
            send_val[i] = recv_val[input_sel]
    
    #recv ports
    for i in range(n_inputs):
        if i != input_sel:
            # Not selected input - not ready
            recv_rdy[i] = 0
        else:
            # Selected input - ready if output is ready
            recv_rdy[i] = send_rdy[output_sel]
    
    return send_msg, send_val, recv_rdy