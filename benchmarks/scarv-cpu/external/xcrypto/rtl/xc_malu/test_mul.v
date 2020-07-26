`include "xc_malu_mul.v"

module test (

input  wire [31:0]  rs1             ,
input  wire [31:0]  rs2             ,

input  wire [ 5:0]  count           ,
input  wire [63:0]  acc             ,
input  wire [31:0]  arg_0           ,

input  wire         carryless       ,

input  wire         pw_32           , // 32-bit width packed elements.
input  wire         pw_16           , // 16-bit width packed elements.
input  wire         pw_8            , //  8-bit width packed elements.
input  wire         pw_4            , //  4-bit width packed elements.
input  wire         pw_2            , //  2-bit width packed elements.

input  wire         lhs_sign        ,
input  wire         rhs_sign        ,

output wire [31:0]  padd_lhs        , // Packed adder left input
output wire [31:0]  padd_rhs        , // Packed adder right input
output wire         padd_sub        , // Packed adder subtract?
output wire         padd_cin        , // Packed adder carry in
output wire         padd_cen        , // Packed adder carry enable.

input  wire [32:0]  padd_cout       ,
input  wire [31:0]  padd_result     ,

output wire [63:0]  n_acc           ,
output wire [31:0]  n_arg_0         ,
output wire         ready

);

xc_malu_mul i_xc_malu_mul (
.rs1        (rs1            ),
.rs2        (rs2            ),
.count      (count          ),
.acc        (acc            ),
.arg_0      (arg_0          ),
.carryless  (mul_carryless  ),
.pw_32      (pw_32          ), // 32-bit width packed elements.
.pw_16      (pw_16          ), // 16-bit width packed elements.
.pw_8       (pw_8           ), //  8-bit width packed elements.
.pw_4       (pw_4           ), //  4-bit width packed elements.
.pw_2       (pw_2           ), //  2-bit width packed elements.
.lhs_sign   (mul_lhs_sign   ),
.rhs_sign   (mul_rhs_sign   ),
.padd_lhs   (mul_padd_lhs   ), // Packed adder left input
.padd_rhs   (mul_padd_rhs   ), // Packed adder right input
.padd_sub   (mul_padd_sub   ), // Packed adder subtract?
.padd_cin   (mul_padd_cin   ), // Packed adder carry in
.padd_cen   (mul_padd_cen   ), // Packed adder carry enable.
.padd_cout  (padd_cout      ), // Packed adder carry out
.padd_result(padd_result    ), // Packed adder result.
.n_acc      (mul_n_acc      ),
.n_arg_0    (mul_n_arg_0    ),
.ready      (mul_ready      )
);

reg [31:0]  padd_lhs_r;
reg [31:0]  padd_rhs_r;
reg         padd_sub_r;
reg         padd_cin_r;
reg         padd_cen_r;
reg [63:0]  n_acc_r;
reg [31:0]  n_arg_0_r;
reg         ready_r;

always @(*) begin
	padd_lhs_r  = padd_lhs;
	padd_rhs_r  = padd_rhs;
	padd_sub_r  = padd_sub;
	padd_cin_r  = padd_cin;
	padd_cen_r  = padd_cen;
	n_acc_r   = n_acc;
	n_arg_0_r = n_arg_0;
	ready_r   = ready;
end

endmodule
