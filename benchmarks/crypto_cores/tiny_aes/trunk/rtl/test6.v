`include "aes_256.v"

module test(clk, in, out_1, out_2);

input              clk;
input      [255:0] in;
output reg [255:0] out_1;
output reg [127:0] out_2;

wire [255:0] tmp_1;
wire [127:0] tmp_2;

expand_key_type_B_256 INSTANCE(clk, in, tmp_1, tmp_2);

always @ (posedge clk)
	out_1 <= tmp_1;

assign out_2 = tmp_2;

endmodule
