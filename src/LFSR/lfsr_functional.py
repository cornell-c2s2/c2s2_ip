import numpy as np

def XOR(a,b):
    if(a == 0 and b == 1):
        return 1
    elif(a == 1 and b == 0):
        return 1
    else:
        return 0

def taps(Q):
    Q1 = Q[1:2]
    Q2 = Q[5:6]
    Q6 = Q[6:7]
    Q31 = Q[31:]

    tap1 = XOR(int(Q1), int(Q2))
    tap2 = XOR(int(Q6), int(Q31))
    return XOR(tap1, tap2)
    

def main():
    '''
    BIST controller side
    '''
    #BIST seeds generated (32 bits)
    num_msgs = 10
    req_msgs = []
    num = np.random.rand(num_msgs) * 1000000000

    for i in range(num_msgs):
        req_msgs.append(bin(int(num[i]))) 
        req_msgs[i] = req_msgs[i][2:]
        
        while(len(req_msgs[i]) <= 32):
            req_msgs[i] += '0'
            #this req_msg does not include the # of loops at the beginning

    

    '''
    Circuit side
    '''
    resq_msgs = []
    
    print("LFSR SOFTWARE REPORT \n______________________________________________\n")
    
    for i in range(num_msgs):
        print("ROUND " + str(i))
        
        Q = req_msgs[i]
        print("Initial Msg: " + Q)

        resq_msgs.append([])

        for j in range(10):
            resq_msgs[i].append(Q)
            print("Tap " + str(j) + ": " + str(taps(Q)))
            Q = Q[1:] + str(taps(Q))
            print("Shifted Msg: " + Q)
            

        testarray = resq_msgs[i]
        for k in range(len(testarray)):
            for h in range(len(testarray)):
                if(k != h and testarray[k] == testarray[h]):
                    print("SAME VALUE DETECTED")

        print("______________________________________________\n")
    
    

if __name__ == "__main__":
    main()