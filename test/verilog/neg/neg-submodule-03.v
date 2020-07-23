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

   test_sub_1 INS1(clk, ct1, in_r, tmp1);
   test_sub_1 INS2(clk, ct2, in_r, tmp2);

   always @(posedge clk) begin
     in_r <= in;
     out1 <= tmp1 + 1;
     out2 <= tmp2 + 1;
   end

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
