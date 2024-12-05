import random

SMALL = 0
LARGE = 1
NEG = 0
POS = 1

def gen_num(size, sign):
    pass

def gen_small():
    return random.randint(0, (1 << 8) - 1)

def gen_large():
    return random.randint(1 << 20, (1 << 32) - 1)

def gen_rand32():
    return random.randint(0, (1 << 32) - 1)



def mask_32bit(x):
    return x & (2 ** 32 - 1)

def gen_large_pos_pos_tests():
    tests = []
    for i in range(30):
        a, b = gen_large(), gen_large()
        prod = mask_32bit(a * b)
        tests.append((a, b, prod))
    return tests

def gen_small_neg_neg_tests():
    tests = []
    for i in range(30):
        a, b = -gen_small(), -gen_small()
        prod = mask_32bit(a * b)
        tests.append((a, b, prod))
    return tests

def print_tests(tests):
    for test in tests:
        print("mk_imsg( %d, %d), mk_omsg( %d),"%test)
    

if __name__ == "__main__":
    # tests = gen_large_pos_pos_tests()
    tests = gen_small_neg_neg_tests()
    print_tests(tests)
