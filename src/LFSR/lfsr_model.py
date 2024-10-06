class LFSRDesign:
    def __init__(self):
        self.state = 'IDLE'  # Initial FSM state
        self.next_state = 'IDLE'
        self.counter = 0
        self.reset = False
        
        self.Q = [0] * 32  # 32-bit register for LFSR
        self.Qin = 0  # Input to be shifted into Q
        
        self.req_val = False
        self.req_msg = [0] * 37
        self.req_rdy = False

        self.resq_rdy = False
        self.resq_msg = [0] * 32
        self.resq_val = False
        

    # XOR Gate function
    def XOR(self, A, B):
        return A ^ B

    # State transition logic
    def update_state(self):
        if self.state == 'IDLE':
            if self.req_val:
                self.next_state = 'GEN_VAL'
            else:
                self.next_state = 'IDLE'
        elif self.state == 'GEN_VAL':
            if self.resq_rdy:
                self.next_state = 'SEND_VAL'
            else:
                self.next_state = 'GEN_VAL'
        elif self.state == 'SEND_VAL':
            if self.counter > 5:
                self.next_state = 'IDLE'
            else:
                self.next_state = 'GEN_VAL'
        else:
            self.next_state = 'IDLE'

    # Action for each state
    def execute_state(self):
        if self.state == 'IDLE':
            self.req_rdy = True
            self.resq_val = False
            self.counter_reset = True
        elif self.state == 'GEN_VAL':
            self.req_rdy = False
            self.resq_val = True
            self.counter_reset = False
        elif self.state == 'SEND_VAL':
            self.req_rdy = False
            self.resq_val = False
            self.counter_reset = False

    # Simulate clock signal and FSM transitions
    def clock_cycle(self):
        if self.reset:
            self.state = 'IDLE'
        else:
            self.state = self.next_state

    # Simulate counter updates every clock cycle
    def counter_cycle(self):
        if self.reset or self.counter_reset:
            self.counter = 0
        elif self.state == 'SEND_VAL':
            self.counter += 1
        else:
            self.counter = self.counter

    # Taps
    def taps(self):
        tap1 = self.XOR(self.Q[1], self.Q[5])
        tap2 = self.XOR(self.Q[6], self.Q[31])
        self.Qin = self.XOR(tap1, tap2)

    def shift(self):
        if self.state == 'GEN_VAL':
            # Shift Q over by 1 bit, shift in Qin from the taps
            for i in reversed(32):
                if(i == 0):
                    self.Q[0] = self.Qin
                else:
                    self.Q[i] = self.Q[i-1]

    #BIST-LFSR Communication
    def BIST_update(self, req_msg, req_val):
        if(req_val == True):
            self.req_val = req_val
            self.req_msg = req_msg
    
    #circuit-LFSR communication
    def circuit_update(self, resq_rdy):
        if(resq_rdy == True):
            self.resq_rdy == resq_rdy
            self.resq_msg == self.Q

    #getters
    def get_resq_msg(self):
        return self.resq_msg
    
    def get_req_msg(self):
        return self.req_msg
    # Overall function to run one clock cycle
    def run_cycle(self):
        self.update_state()
        self.execute_state()
        self.taps()
        self.shift()
        self.clock_cycle()


def main():
    resq_msg_collector = []
