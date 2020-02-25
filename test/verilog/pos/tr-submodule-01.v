module test(clk, in1, out1);
   input clk;
   input in1;
   output reg out1;
   wire        tmp1;

   test_sub_1 INS1(clk, in1, tmp1);
   
   always @(posedge clk)
     out1 <= tmp1 + 1;

endmodule // test

module test_sub_1(clk, in2, out2);
   input clk;
   input in2;
   output reg out2;

   always @(posedge clk)
     out2 <= in2 + 1;

endmodule // test_sub_1

   
