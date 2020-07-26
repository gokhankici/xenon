`include "xc_malu_divrem.v"

module test (

input  wire         clock           ,
input  wire         resetn          ,

input  wire [31:0]  rs1             ,
input  wire [31:0]  rs2             ,

input  wire         valid           ,
input  wire         op_signed       ,
input  wire         flush           ,

input  wire [ 5:0]  count           ,
input  wire [63:0]  acc             , // Divisor
input  wire [31:0]  arg_0           , // Dividend
input  wire [31:0]  arg_1           , // Quotient

output wire [63:0]  n_acc           ,
output wire [31:0]  n_arg_0         ,
output wire [31:0]  n_arg_1         ,
output wire         ready           

);

xc_malu_divrem i_xc_malu_divrem (
.clock      (clock       ),
.resetn     (resetn      ),
.rs1        (rs1         ),
.rs2        (rs2         ),
.valid      (valid       ),
.op_signed  (div_signed  ),
.flush      (flush       ),
.count      (count       ),
.acc        (acc         ), // Divisor
.arg_0      (arg_0       ), // Dividend
.arg_1      (arg_1       ), // Quotient
.n_acc      (div_n_acc   ),
.n_arg_0    (div_n_arg_0 ),
.n_arg_1    (div_n_arg_1 ),
.ready      (div_ready   )
);

reg [63:0]  n_acc_r;
reg [31:0]  n_arg_0_r;
reg [31:0]  n_arg_1_r;
reg         ready_r;

always @(*) begin
	n_acc_r   = n_acc;
	n_arg_0_r = n_arg_0;
	n_arg_1_r = n_arg_1;
	ready_r   = ready;
end

endmodule
