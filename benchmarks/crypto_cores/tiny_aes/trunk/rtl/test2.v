`include "table.v"

module test(
	input  wire         clk, 
	input  wire [127:0] state_in,
	input  wire [127:0] key,
	output reg  [127:0] out
);

wire       [31:0]  s0,  s1,  s2,  s3,
	z0,  z1,  z2,  z3,
	p00, p01, p02, p03,
	p10, p11, p12, p13,
	p20, p21, p22, p23,
	p30, p31, p32, p33,
	k0,  k1,  k2,  k3;

assign k0 = key[127: 96];
assign k1 = key[ 95: 64];
assign k2 = key[ 63: 32];
assign k3 = key[ 31:  0];

assign s0 = state_in[127: 96];
assign s1 = state_in[ 95: 64];
assign s2 = state_in[ 63: 32];
assign s3 = state_in[ 31:  0];

table_lookup
	t0 (clk, s0, p00, p01, p02, p03),
	t1 (clk, s1, p10, p11, p12, p13),
	t2 (clk, s2, p20, p21, p22, p23),
	t3 (clk, s3, p30, p31, p32, p33);

assign z0 = p00 ^ p11 ^ p22 ^ p33 ^ k0;
assign z1 = p03 ^ p10 ^ p21 ^ p32 ^ k1;
assign z2 = p02 ^ p13 ^ p20 ^ p31 ^ k2;
assign z3 = p01 ^ p12 ^ p23 ^ p30 ^ k3;

always @ (posedge clk)
	out <= {z0, z1, z2, z3};

endmodule

