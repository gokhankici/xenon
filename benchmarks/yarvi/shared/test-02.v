`include "yarvi.v"

`define DATA 72
`define ADDR 10

module test(
        input  wire            clk,
        input  wire            wr,
        input  wire [ADDR-1:0] addr,
        input  wire [DATA-1:0] din,
        output reg  [DATA-1:0] dout1,
        output reg  [DATA-1:0] dout2
);

wire [DATA-1:0] a_dout;
wire [DATA-1:0] b_dout;

bram_tdp mem0(
	.a_clk(clock), .a_wr(1'd 0), .a_addr(addr), .a_din(8'h x), .a_dout(a_dout),
	.b_clk(clock), .b_wr(wr),    .b_addr(addr), .b_din(din),   .b_dout(b_dout));


always @(*) begin
        dout1 = a_dout;
        dout2 = b_dout;
end

endmodule
