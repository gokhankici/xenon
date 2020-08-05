module test(clk, cond, in, out);

input  wire clk, cond, in;
output      out;

reg tmp, cond_r, out1, out2;

always @(*)
	tmp = in + 1;

always @(posedge clk) begin
	cond_r <= cond;
	out1   <= in;
	out2   <= tmp;

	if (cond_r)
		out <= out1;
	else
		out <= out2;
end

endmodule
