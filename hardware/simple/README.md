Hardware example — simple Verilog counter

This folder contains a minimal Verilog example (`counter.v`) and a short guide to simulate it locally using `iverilog` + `vvp`.

Files

- `counter.v` — a tiny 8-bit up-counter with synchronous reset.

Simulate

```sh
# install iverilog on Ubuntu: sudo apt install iverilog
iverilog -o counter_tb counter.v
vvp counter_tb
```

The simulation prints the counter values; use this example as a reference for adding RTL and simple testbenches.
