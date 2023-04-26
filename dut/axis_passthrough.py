"""
Testbench for axis_passthrough module.
"""

import shutil
import tempfile
from enum import Enum

import pytest
import vpw
import vpw.axis


class Param(Enum):
    """Module parameter configuration.

    Attributes
    CFG_DWIDTH: Bus width of counter
    GREEDY: Slave ready starts high when greedy set to '1'
    AXIS_DWIDTH: Bus width of AXI-Stream
    """
    CFG_DWIDTH = 32
    GREEDY = 0
    AXIS_DWIDTH = 8


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='axis_passthrough',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'CFG_DWIDTH': Param.CFG_DWIDTH.value,
                                'GREEDY': Param.GREEDY.value,
                                'AXIS_DWIDTH': Param.AXIS_DWIDTH.value},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=False)

    # set defaults for independent module input signals
    vpw.prep("rst", [0])
    vpw.prep("next", [0])
    vpw.prep("count_clear", [0])

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


def test_simple_stream_pass(context):
    """Test passing a stream."""
    up_stream, dn_stream = context
    depth = 16  # depth of stream

    # set module to pass the stream
    vpw.prep("next", [1])

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


def test_simple_stream_drop(context):
    """Test dropping a stream."""
    up_stream, dn_stream = context
    depth = 16  # depth of stream

    # set module to drop the stream
    vpw.prep("next", [0])

    # send test data to module
    send = [n+10 for n in range(depth)]
    up_stream.send(send)
    dn_stream.ready(True)  # turn on down stream interface

    vpw.idle(depth+10)

    # receive test data from module
    if dn_stream.recv():
        assert False, "received data which should be dropped"
