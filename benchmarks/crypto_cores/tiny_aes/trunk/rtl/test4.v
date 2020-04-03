`include "round.v"
`include "table.v"

module test(
	input  wire         clk, 
	input  wire [127:0] state_in,
	input  wire [127:0] key_in,
	output reg  [127:0] out
);

wire [127:0] state_out;

final_round FINAL_ROUND(clk, state_in, key_in, state_out);

always @(*) begin
	out = state_out;
end

endmodule

