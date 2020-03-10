module test(clk);
   input clk;
   reg   x;
   reg   y; 

   reg   Stall;

   always @(posedge clk) begin
      if (Stall) 
        y <= y;
      else
        y <= x + 1;
   end

   wire Stall_wire;

   assign reg_file_input = 0;

   reg_file REG_FILE(clk, reg_file_input, Stall_wire);

   always @(*) begin
     Stall = Stall_wire;
   end

endmodule

module reg_file(clk, regNo, val);
   input wire clk;
   input wire regNo;
   output reg val;

   // 10 x 32-bit registers
   reg [31:0] reg_array [9:0];

   always @(posedge clk ) begin
      val <= reg_array[regNo];
   end
endmodule
