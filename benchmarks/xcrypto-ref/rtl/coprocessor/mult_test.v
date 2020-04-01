// `include "scarv_cop_palu_multiplier.v"
`include "multiplier_stub_1.v"

module mult_test(
input  wire         g_clk            ,
input  wire         g_resetn         ,

input  wire         mul_start        ,
input  wire [31:0]  mul_a            , // LHS operand
input  wire [31:0]  mul_b            , // RHS operand
input  wire [ 2:0]  id_pw            , // Pack width
input  wire         mul_hi           ,
input  wire         mul_ncarry       ,

output reg          mul_done_reg     ,
output reg  [31:0]  mul_result_reg     // Writeback data
);

wire          mul_done;
wire  [31:0]  mul_result;

always @(*) begin
	mul_done_reg = mul_done;
	mul_result_reg = mul_result;
end

scarv_cop_palu_multiplier i_palu_multiplier (
.g_clk   (g_clk     ), // Global clock.
.g_resetn(g_resetn  ), // Global synchronous active low reset
.start   (mul_start ), // Trigger to start multiplying
.done    (mul_done  ), // Signal multiplication has finished.
.a       (mul_a     ), // LHS operand
.b       (mul_b     ), // RHS operand
.pw      (id_pw     ), // Pack width.
.high    (mul_hi    ),
.ncarry  (mul_ncarry),
.result  (mul_result)  // Result of the multiplication.
);

endmodule
