`include "xc_malu_pmul.v"

module test (

input  wire [31:0]  rs1             ,
input  wire [31:0]  rs2             ,

input  wire [ 5:0]  count           ,
input  wire [63:0]  acc             ,
input  wire [31:0]  arg_0           ,
input  wire         carryless       ,

input  wire         pw_16           , // 16-bit width packed elements.
input  wire         pw_8            , //  8-bit width packed elements.
input  wire         pw_4            , //  4-bit width packed elements.
input  wire         pw_2            , //  2-bit width packed elements.

output wire [31:0]  padd_lhs        , // Left hand input
output wire [31:0]  padd_rhs        , // Right hand input.
output wire [ 0:0]  padd_sub        , // Subtract if set, else add.
output wire         padd_cen        ,

input       [32:0]  padd_cout       , // Carry bits
input       [31:0]  padd_result     , // Result of the operation

output wire [63:0]  n_acc   ,
output wire [31:0]  n_arg_0         ,

output wire [63:0]  result          ,

output wire         ready        

);

xc_malu_pmul i_malu_pmul(
.rs1        (rs1            ),
.rs2        (rs2            ),
.count      (count          ),
.acc        (acc            ),
.arg_0      (arg_0          ),
.carryless  (mul_carryless  ),
.pw_16      (pw_16          ), // 16-bit width packed elements.
.pw_8       (pw_8           ), //  8-bit width packed elements.
.pw_4       (pw_4           ), //  4-bit width packed elements.
.pw_2       (pw_2           ), //  2-bit width packed elements.
.padd_lhs   (pmul_padd_lhs  ), // Left hand input
.padd_rhs   (pmul_padd_rhs  ), // Right hand input.
.padd_sub   (pmul_padd_sub  ), // Subtract if set, else add.
.padd_cen   (pmul_padd_cen  ), // Packed adder carry enable.
.padd_cout  (padd_cout      ), // Carry bits
.padd_result(padd_result    ), // Result of the operation
.n_acc      (pmul_n_acc     ),
.n_arg_0    (pmul_n_arg_0   ),
.result     (pmul_result    ),
.ready      (pmul_ready     ) 
);

reg [31:0]  padd_lhs_r;
reg [31:0]  padd_rhs_r;
reg [ 0:0]  padd_sub_r;
reg         padd_cen_r;
reg [63:0]  n_acc_r;
reg [31:0]  n_arg_0_r;
reg [63:0]  result_r;
reg         ready_r;

always @(*) begin
	padd_lhs_r = padd_lhs;
	padd_rhs_r = padd_rhs;
	padd_sub_r = padd_sub;
	padd_cen_r = padd_cen;
	n_acc_r    = n_acc;
	n_arg_0_r  = n_arg_0;
	result_r   = result;
	ready_r    = ready;
end

endmodule
