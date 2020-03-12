module test(clk, ct, in, out1);
   input wire clk;
   input wire in;
   input wire ct;
   output reg out1;

   wire       tmp1;

   test_sub_1 INS1(clk, ct, in, tmp1);

   always @(posedge clk)
     out1 <= tmp1 + 1;

endmodule // test

module test_sub_1(clk, ct, x, y);
   input clk;
   input wire ct;
   input wire x;
   output reg y;
   
   reg        tmp;
   
   always @(posedge clk)
     if (ct)
       begin
          tmp <= x;
          y <= tmp;
       end
     else
       if (x == 0)
         y <= 0;
       else
         begin
            tmp <= x;
            y <= tmp;
         end
endmodule // test_sub_1

   
