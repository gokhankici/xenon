`include "table.v" // REWRITE added this include

module test(
	input  wire         clk, 
	input  wire [31:0]  state,
	output reg  [127:0] out
);

wire [31:0] p0, p1, p2, p3;

table_lookup TABLE_LOOKUP(clk, state, p0, p1, p2, p3);

always @(*) begin
	out = {p3, p2, p1, p0};
end

endmodule
