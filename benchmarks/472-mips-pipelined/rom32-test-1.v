`include "rom32.v"

module test(
	input  wire [31:0] address,
	output reg  [31:0] out
);

wire [31:0] tmp;

rom32 ROM32_INSTANCE(address, tmp);

always @(*) begin
	out = tmp;
end

endmodule
