`include "table.v"

module test(clk, in, out);

input  wire        clk;
input  wire [31:0] in;
output reg  [31:0] out;

wire [31:0] tmp;


S4 S4_INSTANCE(clk, in, tmp);

always @(posedge clk) begin
	out <= tmp;
end

endmodule
