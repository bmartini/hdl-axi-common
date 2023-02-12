# Common HDL AXI modules

Written in SystemVerilog these are some of the modules I've found most useful
in HDL/FPGA projects that use the AXI-Stream and AXI4Lite interfaces.


## AXI Interface

The AXI modules has been designed for easy integration and use with standard
AXI buses or similar. Thus the behavior of the valid/ready bus conforms to
standard AXI usage. Namely:

* Both __valid__ & __ready__ must be asserted for a successful transfer
* __ready__ must only be deasserted directly after a successful transfer
* __valid__ must only be deasserted directly after a successful transfer
* __valid__ being asserted must not depend on __ready__ also being asserted
* __data__  and similar signals must be stable while __valid__ is asserted


## Formal Verification

Assertions are used to model the behavior of the modules for use in formal
verification. To preform the verification proof the open source software
[SymbiYosys](https://symbiyosys.readthedocs.io/en/latest/) and the
configuration files can be found in the [sby](sby) directory.


```bash
sby -f <module name>.sby
```


## Testbench Simulation

Testbenchs are being written for the SystemVerilog modules by leveraging the
[VPW](https://github.com/bmartini/vpw-testbench) and pytest frameworks and can
be found in the [dut](dut) directory.

To run a single test, use the following command.

```bash
pytest -v axi4lite_reg.py
```

To run a single test within a testbench.

```bash
pytest -v axi4lite_reg.py -k test_simple_write_and_read
```

And to run a every test within the current directory.

```bash
pytest -v *.py
```

If you want to generate a waveform to view for debug purposes you must edit the
following line within a testbench.

From:

```python
    vpw.init(design, trace=False)
```

To:

```python
    vpw.init(design, trace=True)
```

And then when you run a single test within that testbench, a waveform will be
created in the current directory.
