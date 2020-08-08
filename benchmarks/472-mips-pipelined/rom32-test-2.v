`include "rom32.v"

module test(
	input  wire        clk,
	input  wire [31:0] address,
	output reg  [31:0] out
);

wire [31:0] tmp;
reg  [31:0] tmp2;

rom32 ROM32_INSTANCE(address, tmp);

always @(posedge clk) begin
	tmp2 <= tmp;

	if (tmp2)
		out <= address;
	else
		out <= tmp2;
end

endmodule
