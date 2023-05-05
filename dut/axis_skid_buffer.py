"""
Testbench for axis_skid_buffer module.
"""

import random
import shutil
import tempfile
from enum import Enum

import pytest
import vpw
import vpw.axis


class Param(Enum):
    """Module parameter configuration.

    Attributes
    GREEDY: Slave ready starts high when greedy set to '1'
    AXIS_DWIDTH: Bus width of AXI-Stream
    """
    GREEDY = 0
    AXIS_DWIDTH = 8


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='axis_skid_buffer',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'GREEDY': Param.GREEDY.value,
                                'AXIS_DWIDTH': Param.AXIS_DWIDTH.value},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=False)

    # set defaults for independent module input signals
    vpw.prep("rst", [0])

    # testbench master controls modules slave (up stream)
    up_stream = vpw.axis.Master("s", Param.AXIS_DWIDTH.value)
    vpw.register(up_stream)

    # testbench slave controls modules master (down stream)
    dn_stream = vpw.axis.Slave("m", Param.AXIS_DWIDTH.value)
    vpw.register(dn_stream)

    # reset module
    vpw.prep("rst", [1])
    vpw.idle(2)
    vpw.prep("rst", [0])
    vpw.idle(10)

    yield up_stream, dn_stream

    vpw.idle(100)
    vpw.finish()


def test_simple_stream(context):
    """Test passing a stream without interruption."""
    up_stream, dn_stream = context
    depth = 16  # depth of stream

    # send test data to module
    send = [n+10 for n in range(depth)]
    up_stream.send(send)
    dn_stream.ready(True)  # turn on down stream interface

    vpw.idle(depth+10)

    # receive test data from module
    recv = dn_stream.recv()
    if not recv:
        assert False, "received no data from module"

    assert send == recv, "received data not the as sent"


def test_simple_stream_interrupted(context):
    """Test passing a stream with interruptions."""
    up_stream, dn_stream = context
    depth = 16  # depth of stream

    # send test data to module
    send = [n+10 for n in range(depth)]
    up_stream.send(send)

    # randomly turn down stream interface on and off
    while len(dn_stream.queue[0]) == 0:
        io = vpw.tick()
        m_tvalid = bool(io["m_tvalid"])
        m_tready = bool(io["m_tready"])

        if (not m_tready) or (m_tvalid and m_tready):
            dn_stream.ready(bool(random.getrandbits(1)))

    vpw.idle(10)

    # receive test data from module
    recv = dn_stream.recv()
    if not recv:
        assert False, "received no data from module"

    assert send == recv, "received data not the as sent"
