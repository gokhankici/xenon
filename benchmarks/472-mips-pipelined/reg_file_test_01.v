`include "reg_file.v"

module test(clk, rw, rn1, rn2, wn, out1, out2, wd);

input             clk;
input             rw;
input      [4:0]  rn1, rn2, wn;
input      [31:0] wd;
output reg [31:0] out1, out2;

reg [31:0] rd1, rd2;

reg_file RF1(.clk(clk), .RegWrite(rw), .RN1(rn1), .RN2(rn2), .WN(wn), .RD1(rd1), .RD2(rd2), .WD(wd));

always @(posedge clk) begin
	out1 <= rd1;
	out2 <= rd2;
end

endmodule
