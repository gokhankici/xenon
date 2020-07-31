module test(clk, ct1, ct2, in, out1, out2);
   input wire clk;
   input wire in;
   input wire ct1;
   input wire ct2;
   output reg out1;
   output reg out2;

   wire       tmp1;
   wire       tmp2;

   reg in_r;

   test_sub_1 INS1(.ct(ct1), .x(in_r), .y(tmp1));

   always @(*) begin
	   if (ct1)
		   tmp2 = 0;
	   else
		   tmp2 = in_r;
   end

   always @(posedge clk)
	   in_r <= in;

   always @(posedge clk)
	   out1 <= tmp1 + 1;

   always @(posedge clk)
	   out2 <= tmp2 + 1;

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
