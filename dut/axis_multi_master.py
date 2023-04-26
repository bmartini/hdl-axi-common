"""
Testbench for axis_multi_master module.
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
    PORT_NB: Number of master interfaces
    """
    GREEDY = 0
    AXIS_DWIDTH = 8
    PORT_NB = 2


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='axis_multi_master',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'GREEDY': Param.GREEDY.value,
                                'AXIS_DWIDTH': Param.AXIS_DWIDTH.value,
                                'PORT_NB': Param.PORT_NB.value},
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
    dn_stream = vpw.axis.Slave("m", Param.AXIS_DWIDTH.value, concat=Param.PORT_NB.value)
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
    dn_stream.ready(True, position=0)  # turn on down stream interface 0
    dn_stream.ready(True, position=1)  # turn on down stream interface 1

    vpw.idle(depth+10)

    # receive test data from module
    recv0 = dn_stream.recv(position=0)
    if not recv0:
        assert False, "received no data from down stream interface 0"

    recv1 = dn_stream.recv(position=1)
    if not recv1:
        assert False, "received no data from down stream interface 1"

    assert send == recv0, "received interface 0 data not the as sent"
    assert send == recv1, "received interface 1 data not the as sent"


def test_simple_stream_interrupted(context):
    """Test passing a stream with interruptions."""
    up_stream, dn_stream = context
    depth = 16  # depth of stream

    # send test data to module
    send = [n+10 for n in range(depth)]
    up_stream.send(send)

    # randomly turn down stream interface on and off
    while up_stream.pending[0] != 0:
        # turn on down stream interface 0
        dn_stream.ready(bool(random.getrandbits(1)), position=0)

        # turn on down stream interface 1
        dn_stream.ready(bool(random.getrandbits(1)), position=1)
        vpw.tick()

    dn_stream.ready(True, position=0)  # turn on down stream interface 0
    dn_stream.ready(True, position=1)  # turn on down stream interface 1
    vpw.idle(10)

    # receive test data from module
    recv0 = dn_stream.recv(position=0)
    if not recv0:
        assert False, "received no data from down stream interface 0"

    recv1 = dn_stream.recv(position=1)
    if not recv1:
        assert False, "received no data from down stream interface 1"

    assert send == recv0, "received interface 0 data not the as sent"
    assert send == recv1, "received interface 1 data not the as sent"
