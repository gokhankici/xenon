module test(clk, a, b, ar, r);
   input clk, a, b;
   input wire ar;

   // @annot{taint_source(a)}
   // @annot{taint_sink(r)}

   wire c;
   output reg  r;
   
   assign c = a & b;

   always @(posedge clk) begin
      r <= c;
   end
   

endmodule
