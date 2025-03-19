import pymtl3
import spi_stream_protocol as spis
import spi_driver_physical as spid
# import src.tapeins.sp24.physical.test_interconnect_physical as testphy

from pymtl3.stdlib.stream.ifcs import valrdy_to_str

import math


# Helper function for interconnect printouts
def pad(n: int) -> str:
  return " " * (3 - len(str(n))) + str(n)


def run_interaction(dut, in_msgs, out_len, max_trsns=100, curr_trsns=0):
  in_msgs = [pymtl3.mk_bits(20)(x) for x in in_msgs]

  in_idx = 0
  out_idx = 0
  trsns = curr_trsns + 1

  spc = 0

  print("")

  while out_idx < out_len:
    if trsns > max_trsns:
      assert False, "Exceeded max transactions"

    if in_idx < len(in_msgs) and spc == 1:
      retmsg = spid.spi_write_physical(dut, spis.write_read_msg(in_msgs[in_idx]))
      spc = retmsg[20]
      print(
        "Trsn" + pad(trsns) + ":",
        valrdy_to_str(in_msgs[in_idx], 1, 1, 6),
        ">",
        valrdy_to_str(retmsg[0:20], retmsg[21], 1, 6),
      )
      if retmsg[21] == 1:
        out_idx += 1
      in_idx += 1

    else:
      retmsg = spid.spi_write_physical(dut, spis.read_msg())
      print(
        "Trsn" + pad(trsns) + ":",
        valrdy_to_str(0, in_idx < len(in_msgs), spc, 6),
        ">",
        valrdy_to_str(retmsg[0:20], retmsg[21], 1, 6),
      )
      spc = retmsg[20]
      if retmsg[21] == 1:
        out_idx += 1

    trsns += 1

  return retmsg


def send(dut, input):
  in_msg = pymtl3.mk_bits(20)(input)

  retmsg = spid.spi_write_physical(dut, spis.write_read_msg(in_msg))
  retmsg2 = spid.spi_write_physical(dut, spis.read_msg())
  print(retmsg)
  print(retmsg2)
  return retmsg2


def config(msg):
  # input = [msg]
  # run_interaction(None, input, 1)
  # spid.spi_write_physical(None, spis.write_read_msg(pymtl3.mk_bits(20)(msg)))
  send(None, msg)


def inject(in_msgs, max=100):
  # return send(None, in_msgs, len(in_msgs), max_trsns=max)
  return send(None, in_msgs)


def fft_inj(in_msgs, max=100):
  assert len(in_msgs) == 32

  for i in range(32):
    retmsg = spid.spi_write_physical(None, spis.write_read_msg(pymtl3.mk_bits(20)(in_msgs[i])))
    # print("injected: ", valrdy_to_str(retmsg[0:20], 1, 1))
    print("injected: ", retmsg[0:20])
  for i in range(16):
    retmsg2 = spid.spi_write_physical(None, spis.read_msg())
    # print("received: ", valrdy_to_str(retmsg2[0:20], 1, 1))\
    print("received: ", retmsg2[0:20])


def gen_wav(amp, freq, n):
  assert amp <= 0x0ffff

  list = []
  for i in range(n):
    list += [amp*math.sin(2*math.pi*freq*i/100)]
  return list