`include "mux3.v"

module test(clk, sel1, sel2, in1, in2, in3, out1, out2);

input wire clk;
input wire in1;
input wire in2;
input wire in3;
input wire [1:0] sel1;
input wire [1:0] sel2;
output reg out1;
output reg out2;
output reg tmp1;
output reg tmp2;

mux3 #(.bandwidth(1)) INS1(.sel(sel1), .a(in1), .b(in2), .c(in3), .y(tmp1));
mux3 #(.bandwidth(1)) INS2(.sel(sel2), .a(in1), .b(in2), .c(in3), .y(tmp2));

always @(posedge clk) begin
	out1 <= tmp1;
	out2 <= tmp2;
end

endmodule
