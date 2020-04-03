`include "table.v"

module test(clk, in, out);

input  wire        clk;
input  wire [31:0] in;
output reg  [31:0] out;

wire [7:0] out_0;
wire [7:0] out_1;
wire [7:0] out_2;
wire [7:0] out_3;

S
	S_0 (clk, in[31:24], out_3),
	S_1 (clk, in[23:16], out_2),
	S_2 (clk, in[15:8],  out_1),
	S_3 (clk, in[7:0],   out_0 );

assign out = {out_3, out_2, out_1, out_0};

endmodule
