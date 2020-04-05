`include "yarvi.v"

`define DATA 72
`define ADDR 10

module test(
        input  wire            clk,
        input  wire            wr,
        input  wire [ADDR-1:0] addr,
        input  wire [DATA-1:0] din,
        output reg  [DATA-1:0] dout
);

wire [DATA-1:0] a_dout;
wire [DATA-1:0] b_dout;

bram_tdp MEM_INSTANCE(
        .a_clk(clk), .a_wr(wr), .a_addr(addr), .a_din(din), .a_dout(a_dout),
        .b_clk(clk), .b_wr(wr), .b_addr(addr), .b_din(din), .b_dout(b_dout)
);

always @(*) begin
        dout = a_dout;
end

endmodule
