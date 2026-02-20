# Hardware examples

This folder contains minimal hardware reference examples intended for demonstration and educational use.

Files

- `simple_counter.v` — a tiny Verilog counter you can simulate with common tools (e.g., Icarus Verilog).

Simulation (example using Icarus Verilog)

```sh
iverilog -o counter_tb hardware/simple_counter.v
vvp counter_tb
```
