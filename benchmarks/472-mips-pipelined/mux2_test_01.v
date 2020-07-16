`include "mux2.v"

module test(clk, sel, in1, in2, out);

input wire clk;
input wire in1;
input wire in2;
input wire [1:0] sel;
output reg out;
output reg tmp;

mux2 #(.bandwidth(1)) INS1(.sel(sel), .a(in1), .b(in2), .y(tmp));

always @(posedge clk) begin
	out <= tmp;
end

endmodule
