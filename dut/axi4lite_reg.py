"""
Testbench for axi4lite_reg module.
"""

import math
import random
import shutil
import tempfile
from enum import Enum
from types import ModuleType
from typing import Generator, List

import pytest
import vpw
import vpw.axi4lite


class Param(Enum):
    """Parameters for module."""
    AXI_DWIDTH = 32
    AXI_AWIDTH = 7


# local parameters within the axi4lite_reg module
CFG_DWIDTH = Param.AXI_DWIDTH.value
CFG_AWIDTH = Param.AXI_AWIDTH.value-int(math.log2(math.ceil(Param.AXI_DWIDTH.value/8)))


class Bram:
    def __init__(self, interface: str, data_width: int, addr_width: int) -> None:
        assert ((data_width % 8) == 0), "Bram data width is not valid"
        assert (addr_width <= 64), "Bram address width is not valid"
        self._interface = interface
        self._data_width = data_width
        self._addr_width = addr_width
        self._ram: List[int] = [0]*(2**addr_width)

    def _wr(self) -> Generator:
        while True:
            io = yield

            if io[f"{self._interface}_wr_en"]:
                wr_data = vpw.unpack(self._data_width, io[f"{self._interface}_wr_data"])
                wr_addr = vpw.unpack(self._addr_width, io[f"{self._interface}_wr_addr"])
                self._ram[wr_addr] = wr_data

    def _rd(self) -> Generator:
        self._dut.prep(f"{self._interface}_rd_data", vpw.pack(self._data_width, 0))

        while True:
            io = yield
            self._dut.prep(f"{self._interface}_rd_data", vpw.pack(self._data_width, 0))

            if io[f"{self._interface}_rd_en"]:
                rd_addr = vpw.unpack(self._addr_width, io[f"{self._interface}_rd_addr"])
                rd_data = self._ram[rd_addr]
                self._dut.prep(f"{self._interface}_rd_data",
                               vpw.pack(self._data_width, rd_data))

    def init(self, dut: ModuleType) -> Generator:
        self._dut: ModuleType = dut
        wr = self._wr()
        rd = self._rd()
        next(wr)
        next(rd)

        while True:
            io = yield
            wr.send(io)
            rd.send(io)


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='axi4lite_reg',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'AXI_DWIDTH': Param.AXI_DWIDTH.value,
                                'AXI_AWIDTH': Param.AXI_AWIDTH.value},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=False)

    axil = vpw.axi4lite.Master("axil", Param.AXI_DWIDTH.value, Param.AXI_AWIDTH.value)
    vpw.register(axil)

    vpw.register(Bram("cfg", CFG_DWIDTH, CFG_AWIDTH))

    yield axil

    vpw.idle(100)
    vpw.finish()


def test_simple_write_and_read(context):
    """Test axi4lite interface with simple, in order write/read."""
    axil = context
    depth = 2**CFG_AWIDTH  # depth of bram (number of registers)

    # write test data over axi4lite to bram
    send = [n+10 for n in range(depth)]
    for addr, value in enumerate(send):
        axil.write(vpw.tick, addr, value)

    vpw.idle(10)

    # read test data over axi4lite from bram
    recv = [0]*len(send)
    for addr in range(len(recv)):
        recv[addr] = axil.read(vpw.tick, addr)

    assert send == recv, "received data not the as sent"


def test_random_write_and_read(context):
    """Test axi4lite interface with simple, in order write/read."""
    axil = context
    depth = 2**CFG_AWIDTH  # depth of bram (number of registers)

    for x in range(1000):
        send = x + 1
        addr = random.randrange(0, depth)

        # write test data over axi4lite to bram
        axil.write(vpw.tick, addr, send)

        # read test data over axi4lite from bram
        recv = axil.read(vpw.tick, addr)

        assert send == recv, "received data not the as sent"
