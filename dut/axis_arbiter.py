"""
Testbench for axis_arbiter module.
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
    AXIS_DWIDTH: Bus width of AXI-Stream
    PORT_NB: Number of master interfaces
    """
    AXIS_DWIDTH = 8
    PORT_NB = 2


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='axis_arbiter',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'AXIS_DWIDTH': Param.AXIS_DWIDTH.value,
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
    up_stream = vpw.axis.Master("s", Param.AXIS_DWIDTH.value, concat=Param.PORT_NB.value)
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
    send0 = [n+1 for n in range(depth)]
    send1 = [n+16 for n in range(depth)]
    up_stream.send(send0, position=0)
    vpw.idle(2)

    up_stream.send(send1, position=1)
    dn_stream.ready(True)  # turn on down stream interface
    vpw.idle(2*depth+10)

    # receive test data from module
    recv0 = dn_stream.recv()
    if not recv0:
        assert False, "received no data from down stream interface"

    assert send0 == recv0, "received data not the as sent first"

    recv1 = dn_stream.recv()
    if not recv1:
        assert False, "received no data from down stream interface"

    assert send1 == recv1, "received data not the as sent second"
