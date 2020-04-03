`include "round.v"
`include "table.v"

module test(
	input  wire         clk, 
	input  wire [127:0] state_in,
	input  wire [127:0] key_in,
	output reg  [127:0] out
);

reg [127:0] state_out;
wire [31:0] s0,  s1,  s2,  s3,
	z0,  z1,  z2,  z3,
	k0,  k1,  k2,  k3;
wire [7:0]  p00, p01, p02, p03,
	p10, p11, p12, p13,
	p20, p21, p22, p23,
	p30, p31, p32, p33;

assign k0 = key_in[127: 96];
assign k1 = key_in[ 95: 64];
assign k2 = key_in[ 63: 32];
assign k3 = key_in[ 31:  0];

assign s0 = state_in[127: 96];
assign s1 = state_in[ 95: 64];
assign s2 = state_in[ 63: 32];
assign s3 = state_in[ 31:  0];

wire [31:0] x,y,z,t;

assign p00 = x[ 7: 0];
assign p01 = x[15: 8];
assign p02 = x[23:16];
assign p03 = x[31:24];

assign p10 = y[ 7: 0];
assign p11 = y[15: 8];
assign p12 = y[23:16];
assign p13 = y[31:24];

assign p20 = z[ 7: 0];
assign p21 = z[15: 8];
assign p22 = z[23:16];
assign p23 = z[31:24];

assign p30 = t[ 7: 0];
assign p31 = t[15: 8];
assign p32 = t[23:16];
assign p33 = t[31:24];

S4
	S4_1 (clk, s0, x),
	S4_2 (clk, s1, y),
	S4_3 (clk, s2, z),
	S4_4 (clk, s3, t);

assign z0 = {p00, p11, p22, p33} ^ k0;
assign z1 = {p10, p21, p32, p03} ^ k1;
assign z2 = {p20, p31, p02, p13} ^ k2;
assign z3 = {p30, p01, p12, p23} ^ k3;

always @ (posedge clk)
	state_out <= {z0, z1, z2, z3};

always @(*) begin
	out = state_out;
end

endmodule

