`include "xc_malu_mul.v"

module test (

input  wire         clock           ,
input  wire         resetn          ,

input  wire [31:0]  rs1             , //
input  wire [31:0]  rs2             , //
input  wire [31:0]  rs3             , //

input  wire         flush           , // Flush state / pipeline progress
input  wire         valid           , // Inputs valid.

input  wire         do_div          , //
input  wire         do_divu         , //
input  wire         do_rem          , //
input  wire         do_remu         , //
input  wire         do_mul          , //
input  wire         do_mulu         , //
input  wire         do_mulsu        , //
input  wire         do_clmul        , //
input  wire         do_pmul         , //
input  wire         do_pclmul       , //

input  wire         pw_32           , // 32-bit width packed elements.
input  wire         pw_16           , // 16-bit width packed elements.
input  wire         pw_8            , //  8-bit width packed elements.
input  wire         pw_4            , //  4-bit width packed elements.
input  wire         pw_2            , //  2-bit width packed elements.

input  wire [ 5:0]  count           , // Current count value
input  wire [63:0]  acc             , // Current accumulator value
input  wire [31:0]  arg_0           , // Current arg 0 value
input  wire [31:0]  arg_1           , // Current arg 1 value

output wire [63:0]  n_acc           , // Next accumulator value
output wire [31:0]  n_arg_0         , // Next arg 0 value

output wire [31:0]  padd_lhs        , // Packed adder left input
output wire [31:0]  padd_rhs        , // Packed adder right input
output wire         padd_sub        , // Packed adder subtract?
output wire         padd_cin        , // Packed adder carry in
output wire         padd_cen        , // Packed adder carry enable.

input  wire [32:0]  padd_cout       ,
input  wire [31:0]  padd_result     ,

output wire [63:0]  result          , // 64-bit result
output wire         ready             // Outputs ready.

);

wire route_mul = do_mul || do_mulu   || do_mulsu || do_clmul    ;

//
// Submodule interface wires
// -----------------------------------------------------------------

wire         mul_carryless= do_clmul || do_pclmul;
wire         mul_lhs_sign = do_mul   || do_mulsu ;
wire         mul_rhs_sign = do_mul               ;
wire [31:0]  mul_padd_lhs        ; // Packed adder left input
wire [31:0]  mul_padd_rhs        ; // Packed adder right input
wire         mul_padd_sub        ; // Packed adder subtract?
wire         mul_padd_cin        ; // Packed adder carry in
wire         mul_padd_cen        ; // Packed adder carry enable.
wire [63:0]  mul_n_acc           ;
wire [31:0]  mul_n_arg_0         ;
wire         mul_ready           ;
wire [63:0]  mul_result   = acc;

//
// Routing to parent module
// -----------------------------------------------------------------

assign n_acc    = {64{route_mul }} &  mul_n_acc    ;

assign n_arg_0  = {32{route_mul }} &  mul_n_arg_0  ;

assign padd_lhs = {32{route_mul }} &  mul_padd_lhs ;

assign padd_rhs = {32{route_mul }} &  mul_padd_rhs ;

assign padd_sub = route_mul   &&  mul_padd_sub  ;

assign padd_cin =     route_mul   &&  mul_padd_cin ;

assign padd_cen =     route_mul   &&  mul_padd_cen ;

assign result   =  {64{route_mul }} &  mul_result   ;

assign ready    = route_mul   &&  mul_ready ;

//
// Submodule instances.
// -----------------------------------------------------------------

//
// Handles instructions:
//  - mul
//  - mulh
//  - mulhu
//  - mulhsu
//  - clmul
//  - clmulh
//
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


endmodule
