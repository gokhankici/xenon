`include "mux2.v"

module test(clk, sel, in1, in2, out);

input wire clk;
input wire in1;
input wire in2;
input wire [1:0] sel;
output reg out;

reg in1_tmp;
reg in2_tmp;
reg in2_tmp2;
reg out_tmp;

mux2 #(.bandwidth(1)) INS1(.sel(sel), .a(in1_tmp), .b(in2_tmp2), .y(out_tmp));

always @(posedge clk) begin
	in1_tmp <= in1;
	in2_tmp <= in2;
	in2_tmp2 <= in2_tmp;
	out <= out_tmp;
end

endmodule
