module test(clk, ct, in, out);
   input wire clk;
   input wire in;
   input wire ct;
   output reg out;

   wire tmp;
   reg  in_r;

   test_sub_1 INS1(.ct(ct), .x(in_r), .y(tmp));

   always @(posedge clk) begin
	   in_r <= in;
	   out <= tmp + 1;
   end

endmodule // test

module test_sub_1(ct, x, y);
   input clk;
   input wire ct;
   input wire x;
   output reg y;

   always @(*) begin
	   if (ct)
		   y = 0;
	   else
		   y = x;
   end
endmodule // test_sub_1
