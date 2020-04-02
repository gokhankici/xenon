`include "round.v"
`include "table.v"

module test(
	input  wire         clk, 
	input  wire [127:0] state_in,
	input  wire [127:0] key,
	output reg  [127:0] out
);

wire [127:0] state_out;

one_round ONE_ROUND(clk, state_in, key, state_out);

always @(*) begin
	out = state_out;
end

endmodule

