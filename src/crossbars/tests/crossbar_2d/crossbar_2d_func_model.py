import math

def crossbar_2d_func_model(recv_msg, recv_val, send_rdy, control, n_inputs, n_outputs, entries):
    """
    recv_msg: List of lists: recv_msg[N_INPUTS][ENTRIES]
    recv_val: List of N_INPUTS integers (0/1)
    send_rdy: List of N_OUTPUTS integers (0/1)
    control: Integer value of control
    Returns:
        send_msg, send_val, recv_rdy
    """
    input_sel_bits = math.ceil(math.log2(n_inputs))
    output_sel_bits = math.ceil(math.log2(n_outputs))
    control_bit_width = input_sel_bits + output_sel_bits

    input_sel = (control >> (control_bit_width - input_sel_bits)) & ((1 << input_sel_bits) - 1)
    output_sel = (control >> (control_bit_width - input_sel_bits - output_sel_bits)) & ((1 << output_sel_bits) - 1)

    send_msg = [[0] * entries for _ in range(n_outputs)]
    send_val = [0] * n_outputs
    recv_rdy = [0] * n_inputs
    #comb
    for i in range(n_outputs):
        if i != output_sel:
            send_msg[i] = [0] * entries
            send_val[i] = 0
        else:
            if recv_val[input_sel]:
                send_msg[i] = list(recv_msg[input_sel])
                send_val[i] = 1
            else:
                send_msg[i] = [0] * entries
                send_val[i] = 0

    # recv ports
    for i in range(n_inputs):
        if i != input_sel:
            recv_rdy[i] = 0
        else:
            recv_rdy[i] = send_rdy[output_sel]

    return send_msg, send_val, recv_rdy
