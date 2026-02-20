// Simple 4-bit up-counter with enable and synchronous reset
module simple_counter (
    input wire clk,
    input wire rst_n,
    input wire en,
    output reg [3:0] count
);

always @(posedge clk) begin
    if (!rst_n)
        count <= 4'd0;
    else if (en)
        count <= count + 1'b1;
end

endmodule

// Testbench (simple): compile and run with Icarus Verilog for a quick smoke test.
`ifdef TESTBENCH
module tb();
  reg clk = 0;
  reg rst_n = 0;
  reg en = 1;
  wire [3:0] count;

  simple_counter uut(.clk(clk), .rst_n(rst_n), .en(en), .count(count));

  always #5 clk = ~clk;

  initial begin
    #10 rst_n = 1;
    #200 $finish;
  end
endmodule
`endif
