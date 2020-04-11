module test(clk, a, b, r);
   input clk, a, b;
   // input wire ar;

   // @annot{taint_source(a)}
   // @annot{taint_source(b)}
   // @annot{taint_sink(r)}

   wire r1;
   output reg r;
   
   // assign r1 = r + 1; // r1 = r + 1
   // t0
   always @(*) begin
       r1 = r + 1; // TR_t0(r,r1,r',r1') := (r1' = r + 1) && (r' = r)
   end

   // t1
   always @(posedge clk) begin
      r <= r1; // TR_t1(r,r1,r',r1') := (r' = r1) && (r1' = r1)
   end

   // inv_t0(r, r1) && inv_t1(r, r1) && TR_t0(r,r1,r',r1') && ... ==> inv_t1(r', r1')
   // inv_t0(r, r1) && inv_t1(r, r1) && TR_t1(r,r1,r',r1') && ... ==> inv_t0(r', r1')
   
   // inv_t0(r,r1) := ct(r1) && ct(r)
   // inv_t1(r,r1) := ct(r1) && ct(r)

   // inv_t0(r,r1) := ct(r1)
   // inv_t1(r,r1) := ct(r)
   
endmodule
