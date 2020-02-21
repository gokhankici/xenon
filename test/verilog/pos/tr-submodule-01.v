module test(clk, in, out);
   input clk;
   input in;
   output reg out;
   wire        tmp;

   test_sub_1 INS1(clk, in, tmp);
   
   always @(posedge clk)
     out <= tmp + 1;

endmodule // test

module test_sub_1(clk, in, out);
   input clk;
   input in;
   output reg out;

   always @(posedge clk)
     out <= in + 1;

endmodule // test_sub_1

   
