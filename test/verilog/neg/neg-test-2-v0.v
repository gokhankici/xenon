module test(clk);
   input wire clk;
   reg        x;
   reg        y; 
   wire       stall;

   mB MB1(clk, stall);

   always @(posedge clk) begin
      if (stall) 
        y <= y;
      else
        y <= x + 1;
   end

endmodule

module mB(clk, o2);
   input wire clk;
   output reg o2;
   reg        tmp2;
   
   always @(posedge clk)
     o2 <= tmp2;
endmodule
