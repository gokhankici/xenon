module test_sub_1(clk, x, y);
input clk;
input wire x;
output reg y;

always @(posedge clk) y <= x;

endmodule // test_sub_1

module test(clk, cond, in, out);
input wire clk;
input wire in;
input wire cond;
output reg out;

wire       tmp1;
wire       tmp2;

reg in_r;

test_sub_1 INS1(clk, in_r, tmp1);
test_sub_1 INS2(clk, in_r, tmp2);

always @(posedge clk) begin
	in_r <= in;
	if (cond)
		out <= tmp1 + 1;
	else
		out <= tmp2 + 1;
end

endmodule // test

