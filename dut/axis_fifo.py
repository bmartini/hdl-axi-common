"""
Testbench for axis_fifo module.
"""

import random
import shutil
import tempfile
from enum import Enum

import pytest
import vpw
import vpw.axis


class Param(Enum):
    """Parameters for module."""
    DATA_WIDTH = 8
    ADDR_WIDTH = 4


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='axis_fifo',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'DATA_WIDTH': Param.DATA_WIDTH.value,
                                'ADDR_WIDTH': Param.ADDR_WIDTH.value},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=False)

    # testbench master controls modules slave (up stream)
    up_stream = vpw.axis.Master("s", Param.DATA_WIDTH.value)
    vpw.register(up_stream)

    # testbench slave controls modules master (down stream)
    dn_stream = vpw.axis.Slave("m", Param.DATA_WIDTH.value)
    vpw.register(dn_stream)

    yield up_stream, dn_stream

    vpw.idle(100)
    vpw.finish()


def test_simple_stream(context):
    """Test sending and receiving data though the axis fifo."""
    up_stream, dn_stream = context
    depth = 2**Param.ADDR_WIDTH.value  # depth of bram within the fifo

    # send test data to fifo
    send = [n+10 for n in range(depth)]
    up_stream.send(send)
    dn_stream.ready(True)  # turn on down stream interface

    vpw.idle(depth+10)

    # receive test data from fifo
    recv = dn_stream.recv()
    if not recv:
        assert False, "no data received from FIFO"

    assert send == recv, "received data not the as sent"


def test_simple_long_stream(context):
    """Test sending and receiving lots of data."""
    up_stream, dn_stream = context
    depth = 2**Param.ADDR_WIDTH.value  # depth of bram within the fifo

    # send test data to fifo
    send = [n+10 for n in range(2*depth)]
    up_stream.send(send)
    dn_stream.ready(True)  # turn on down stream interface

    vpw.idle(2*depth+10)

    # receive test data from fifo
    recv = dn_stream.recv()
    if not recv:
        assert False, "no data received from FIFO"

    assert send == recv, "received data not the as sent"


def test_intermittent_send_stream(context):
    """Test sending intermittent data stream."""
    up_stream, dn_stream = context
    depth = 2**Param.ADDR_WIDTH.value  # depth of bram within the fifo

    # send test data to fifo
    send = [n+10 for n in range(2*depth)]
    up_stream.send(send)

    while len(up_stream.queue[0]) != 0:
        up_stream.pause(bool(random.getrandbits(1)))
        dn_stream.ready(bool(random.getrandbits(1)))
        vpw.tick()

    while len(dn_stream.queue[0]) == 0:
        dn_stream.ready(bool(random.getrandbits(1)))
        vpw.tick()

    vpw.idle(10)

    # receive test data from fifo
    recv = dn_stream.recv()
    if not recv:
        assert False, "no data received from FIFO"

    assert send == recv, "received data not the as sent"
