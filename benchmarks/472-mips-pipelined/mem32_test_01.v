`include "mem32.v"

module test(clk, addr, mread, mwrite, din, out);

input wire clk;
input wire mread;
input wire mwrite;
input wire [31:0] addr;
input wire [31:0] din;
output reg [31:0] out;
output reg [31:0] tmp;

mem32 INS1(.clk(clk)
          ,.mem_read(mread)
		  ,.mem_write(mwrite)
		  ,.address(addr) // 32 bit
		  ,.data_in(din) // 32 bit
		  ,.data_out(tmp) // 32 bit
		  );

always @(posedge clk) begin
	out <= tmp;
end

endmodule
