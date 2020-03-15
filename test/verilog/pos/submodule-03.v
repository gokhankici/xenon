module test(clk, ct1, ct2, in, out1, out2);
   input wire clk;
   input wire in;
   input wire ct1;
   input wire ct2;
   output reg out1;
   output reg out2;

   wire       tmp1;
   wire       tmp2;

   test_sub_1 INS1(clk, ct1, in, tmp1);
   test_sub_1 INS2(clk, ct2, in, tmp2);

   always @(posedge clk)
     out1 <= tmp1 + 1;

   always @(posedge clk)
     out2 <= tmp2 + 1;

endmodule // test

module test_sub_1(clk, ct, x, y);
   input clk;
   input wire ct;
   input wire x;
   output reg y;

   always @(posedge clk)
     if (ct)
       y <= 0;
     else
       y <= x;
endmodule // test_sub_1
