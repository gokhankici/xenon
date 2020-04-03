`include "table.v"
`include "round.v"

module test(clk, in, out_1, out_2);

input              clk;
input      [255:0] in;
output reg [255:0] out_1;
output reg [127:0] out_2;

wire       [31:0]  k0, k1, k2, k3, k4, k5, k6, k7, v5, v6, v7;
reg        [31:0]  k0a, k1a, k2a, k3a, k4a, k5a, k6a, k7a;
wire       [31:0]  k0b, k1b, k2b, k3b, k4b, k5b, k6b, k7b, k8a;

assign k0 = in[255:224];
assign k1 = in[223:192];
assign k2 = in[191:160];
assign k3 = in[159:128];
assign k4 = in[127: 96];
assign k5 = in[ 95: 64];
assign k6 = in[ 63: 32];
assign k7 = in[ 31:  0];

assign v5 = k4 ^ k5;
assign v6 = v5 ^ k6;
assign v7 = v6 ^ k7;

always @ (posedge clk) begin
	k0a <= k0;
	k1a <= k1;
	k2a <= k2;
	k3a <= k3;
	k4a <= k4;
	k5a <= v5;
	k6a <= v6;
	k7a <= v7;
end

S4 S4_0 (clk, k3, k8a);

assign k0b = k0a;
assign k1b = k1a;
assign k2b = k2a;
assign k3b = k3a;

assign k4b = k4a ^ k8a;
assign k5b = k5a ^ k8a;
assign k6b = k6a ^ k8a;
assign k7b = k7a ^ k8a;

always @ (posedge clk)
	out_1 <= {k0b, k1b, k2b, k3b, k4b, k5b, k6b, k7b};

assign out_2 = {k4b, k5b, k6b, k7b};

endmodule
