module test (
	input wire clk,
	input wire reset,
	input wire start,
	output reg out
);

wire tmp;

ma SUB1(clk, reset, start, tmp);

always @(*) begin
	out = tmp;
end

endmodule



module ma (
	input wire clk,
	input wire reset,
	input wire start,
	output reg ctr
);

wire n_ctr;

always @(*) begin
	n_ctr = ctr + 1;
end

always @(posedge clk) begin
	if (reset)
		ctr <= 0;
	else if(ctr == 0 && !start) begin
		// Do nothing, wait for start
	end else if(start)
		ctr <= n_ctr;
end

endmodule
