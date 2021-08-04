module stalling_cpu(clk);
 input clk;

   wire [31:0] IF_pc;
   reg [31:0] ID_instr, IF_instr;
   reg [4:0]  EX_rt,ID_rt;
   
   
   assign ID_rt = ID_instr[20:16];
   assign IF_instr = IF_pc;
   
   assign Stall = ( ID_rt == EX_rt );

  always @( posedge clk) begin
    if ( Stall == 1) begin
       ID_instr <= ID_instr;
       EX_rt <= EX_rt;
    end else begin
       ID_instr <= IF_instr;
       EX_rt <= ID_rt;
    end
  end
endmodule
