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
[SymbiYosys](https://symbiyosys.readthedocs.io/en/latest/).


```bash
sby -f <module name>.sby
```
