module test(clk, cond, in, out);

input      clk, cond, in;
output reg out;
reg        cond_r;

function [0:0] foo;
	input sel;
	input a;
	input b;

	foo = sel ? a : b;
endfunction

always @(posedge clk) begin
	cond_r <= cond;
	out <= foo(cond_r, in, 0);
end

endmodule
