// Simple 8-bit up-counter with synchronous reset
module counter(
  input wire clk,
  input wire rst_n,
  output reg [7:0] value
);

  always @(posedge clk) begin
    if (!rst_n)
      value <= 8'd0;
    else
      value <= value + 1'b1;
  end

endmodule

// Testbench
`ifdef FORMAL
// formal tools typically drive signals differently; placeholder
`endif

`ifdef SIM
module tb;
  reg clk = 0;
  reg rst_n = 0;
  wire [7:0] value;

  counter uut(.clk(clk), .rst_n(rst_n), .value(value));

  always #5 clk = ~clk; // 100MHz-ish for quick sim

  initial begin
    $dumpfile("counter.vcd");
    $dumpvars(0, tb);
    rst_n = 0;
    #12 rst_n = 1;
    #200 $display("Final value=%d", value);
    #10 $finish;
  end
endmodule
`endif
