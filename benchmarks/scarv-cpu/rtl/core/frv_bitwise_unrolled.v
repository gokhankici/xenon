
//
// module: frv_bitwise
//
//  This module is responsible for many of the bitwise operations the
//  core performs, both from XCrypto and Bitmanip
//

`ifndef FRV_BITWISE_DEFINED
`define FRV_BITWISE_DEFINED

`include "b_lut_unrolled.v"
`include "b_bop_unrolled.v"

module frv_bitwise (

input  wire [31:0]  rs1             , //
input  wire [31:0]  rs2             , //
input  wire [31:0]  rs3             , //

input  wire [ 7:0]  bop_lut         , // LUT for xc.bop

input  wire         flush           , // Flush state / pipeline progress
input  wire         valid           , // Inputs valid.

input  wire         uop_fsl         , // Funnel shift Left
input  wire         uop_fsr         , // Funnel shift right
input  wire         uop_mror        , // Wide rotate right
input  wire         uop_cmov        , // Conditional move
input  wire         uop_lut         , // xc.lut
input  wire         uop_bop         , // xc.bop

output wire [63:0]  result          , // 64-bit result
output wire         ready             // Outputs ready.

);


//
// XCrypto feature class config bits.
parameter XC_CLASS_BIT        = 1'b1;

//
// CMOV
// ------------------------------------------------------------

wire [31:0] result_cmov = |rs2 ? rs1 : rs3;

//
// Rotate/Funnel Shift
// ------------------------------------------------------------

wire [ 5:0] ramt    = uop_mror ? rs3[5:0] : rs2[5:0];

wire [63:0] rword_r = {rs1, uop_mror ? rs2 : rs3};
wire [63:0] rword_l;

wire [63:0] r_in    = uop_fsl ? rword_l : rword_r;

wire [63:0] rt_5    = ramt[5] ? {r_in[31:0], r_in[63:32]} : r_in;   // 32
wire [63:0] rt_4    = ramt[4] ? {rt_5[15:0], rt_5[63:16]} : rt_5;   // 16
wire [63:0] rt_3    = ramt[3] ? {rt_4[ 7:0], rt_4[63: 8]} : rt_4;   // 8
wire [63:0] rt_2    = ramt[2] ? {rt_3[ 3:0], rt_3[63: 4]} : rt_3;   // 4
wire [63:0] rt_1    = ramt[1] ? {rt_2[ 1:0], rt_2[63: 2]} : rt_2;   // 2
wire [63:0] rt_0    = ramt[0] ? {rt_1[   0], rt_1[63: 1]} : rt_1;   // 1

wire [63:0] rout_l  ;

wire [63:0] r_out   = uop_fsl ? rout_l  : rt_0   ;

assign rword_l_0  = rword_r[63];
assign rword_l_1  = rword_r[62];
assign rword_l_2  = rword_r[61];
assign rword_l_3  = rword_r[60];
assign rword_l_4  = rword_r[59];
assign rword_l_5  = rword_r[58];
assign rword_l_6  = rword_r[57];
assign rword_l_7  = rword_r[56];
assign rword_l_8  = rword_r[55];
assign rword_l_9  = rword_r[54];
assign rword_l_10 = rword_r[53];
assign rword_l_11 = rword_r[52];
assign rword_l_12 = rword_r[51];
assign rword_l_13 = rword_r[50];
assign rword_l_14 = rword_r[49];
assign rword_l_15 = rword_r[48];
assign rword_l_16 = rword_r[47];
assign rword_l_17 = rword_r[46];
assign rword_l_18 = rword_r[45];
assign rword_l_19 = rword_r[44];
assign rword_l_20 = rword_r[43];
assign rword_l_21 = rword_r[42];
assign rword_l_22 = rword_r[41];
assign rword_l_23 = rword_r[40];
assign rword_l_24 = rword_r[39];
assign rword_l_25 = rword_r[38];
assign rword_l_26 = rword_r[37];
assign rword_l_27 = rword_r[36];
assign rword_l_28 = rword_r[35];
assign rword_l_29 = rword_r[34];
assign rword_l_30 = rword_r[33];
assign rword_l_31 = rword_r[32];
assign rword_l_32 = rword_r[31];
assign rword_l_33 = rword_r[30];
assign rword_l_34 = rword_r[29];
assign rword_l_35 = rword_r[28];
assign rword_l_36 = rword_r[27];
assign rword_l_37 = rword_r[26];
assign rword_l_38 = rword_r[25];
assign rword_l_39 = rword_r[24];
assign rword_l_40 = rword_r[23];
assign rword_l_41 = rword_r[22];
assign rword_l_42 = rword_r[21];
assign rword_l_43 = rword_r[20];
assign rword_l_44 = rword_r[19];
assign rword_l_45 = rword_r[18];
assign rword_l_46 = rword_r[17];
assign rword_l_47 = rword_r[16];
assign rword_l_48 = rword_r[15];
assign rword_l_49 = rword_r[14];
assign rword_l_50 = rword_r[13];
assign rword_l_51 = rword_r[12];
assign rword_l_52 = rword_r[11];
assign rword_l_53 = rword_r[10];
assign rword_l_54 = rword_r[9 ];
assign rword_l_55 = rword_r[8 ];
assign rword_l_56 = rword_r[7 ];
assign rword_l_57 = rword_r[6 ];
assign rword_l_58 = rword_r[5 ];
assign rword_l_59 = rword_r[4 ];
assign rword_l_60 = rword_r[3 ];
assign rword_l_61 = rword_r[2 ];
assign rword_l_62 = rword_r[1 ];
assign rword_l_63 = rword_r[0 ];

assign rword_l = { rword_l_0 , rword_l_1 , rword_l_2 , rword_l_3 , rword_l_4 , rword_l_5 , rword_l_6 , rword_l_7 , rword_l_8 , rword_l_9
                 , rword_l_10 , rword_l_11 , rword_l_12 , rword_l_13 , rword_l_14 , rword_l_15 , rword_l_16 , rword_l_17 , rword_l_18 , rword_l_19
                 , rword_l_20 , rword_l_21 , rword_l_22 , rword_l_23 , rword_l_24 , rword_l_25 , rword_l_26 , rword_l_27 , rword_l_28 , rword_l_29
                 , rword_l_30 , rword_l_31 , rword_l_32 , rword_l_33 , rword_l_34 , rword_l_35 , rword_l_36 , rword_l_37 , rword_l_38 , rword_l_39
                 , rword_l_40 , rword_l_41 , rword_l_42 , rword_l_43 , rword_l_44 , rword_l_45 , rword_l_46 , rword_l_47 , rword_l_48 , rword_l_49
                 , rword_l_50 , rword_l_51 , rword_l_52 , rword_l_53 , rword_l_54 , rword_l_55 , rword_l_56 , rword_l_57 , rword_l_58 , rword_l_59
                 , rword_l_60 , rword_l_61 , rword_l_62 , rword_l_63
				 };

assign rout_l_0  = rt_0[63];
assign rout_l_1  = rt_0[62];
assign rout_l_2  = rt_0[61];
assign rout_l_3  = rt_0[60];
assign rout_l_4  = rt_0[59];
assign rout_l_5  = rt_0[58];
assign rout_l_6  = rt_0[57];
assign rout_l_7  = rt_0[56];
assign rout_l_8  = rt_0[55];
assign rout_l_9  = rt_0[54];
assign rout_l_10 = rt_0[53];
assign rout_l_11 = rt_0[52];
assign rout_l_12 = rt_0[51];
assign rout_l_13 = rt_0[50];
assign rout_l_14 = rt_0[49];
assign rout_l_15 = rt_0[48];
assign rout_l_16 = rt_0[47];
assign rout_l_17 = rt_0[46];
assign rout_l_18 = rt_0[45];
assign rout_l_19 = rt_0[44];
assign rout_l_20 = rt_0[43];
assign rout_l_21 = rt_0[42];
assign rout_l_22 = rt_0[41];
assign rout_l_23 = rt_0[40];
assign rout_l_24 = rt_0[39];
assign rout_l_25 = rt_0[38];
assign rout_l_26 = rt_0[37];
assign rout_l_27 = rt_0[36];
assign rout_l_28 = rt_0[35];
assign rout_l_29 = rt_0[34];
assign rout_l_30 = rt_0[33];
assign rout_l_31 = rt_0[32];
assign rout_l_32 = rt_0[31];
assign rout_l_33 = rt_0[30];
assign rout_l_34 = rt_0[29];
assign rout_l_35 = rt_0[28];
assign rout_l_36 = rt_0[27];
assign rout_l_37 = rt_0[26];
assign rout_l_38 = rt_0[25];
assign rout_l_39 = rt_0[24];
assign rout_l_40 = rt_0[23];
assign rout_l_41 = rt_0[22];
assign rout_l_42 = rt_0[21];
assign rout_l_43 = rt_0[20];
assign rout_l_44 = rt_0[19];
assign rout_l_45 = rt_0[18];
assign rout_l_46 = rt_0[17];
assign rout_l_47 = rt_0[16];
assign rout_l_48 = rt_0[15];
assign rout_l_49 = rt_0[14];
assign rout_l_50 = rt_0[13];
assign rout_l_51 = rt_0[12];
assign rout_l_52 = rt_0[11];
assign rout_l_53 = rt_0[10];
assign rout_l_54 = rt_0[9 ];
assign rout_l_55 = rt_0[8 ];
assign rout_l_56 = rt_0[7 ];
assign rout_l_57 = rt_0[6 ];
assign rout_l_58 = rt_0[5 ];
assign rout_l_59 = rt_0[4 ];
assign rout_l_60 = rt_0[3 ];
assign rout_l_61 = rt_0[2 ];
assign rout_l_62 = rt_0[1 ];
assign rout_l_63 = rt_0[0 ];

assign rout_l = { rout_l_0 , rout_l_1 , rout_l_2 , rout_l_3 , rout_l_4 , rout_l_5 , rout_l_6 , rout_l_7 , rout_l_8 , rout_l_9
                , rout_l_10 , rout_l_11 , rout_l_12 , rout_l_13 , rout_l_14 , rout_l_15 , rout_l_16 , rout_l_17 , rout_l_18 , rout_l_19
                , rout_l_20 , rout_l_21 , rout_l_22 , rout_l_23 , rout_l_24 , rout_l_25 , rout_l_26 , rout_l_27 , rout_l_28 , rout_l_29
                , rout_l_30 , rout_l_31 , rout_l_32 , rout_l_33 , rout_l_34 , rout_l_35 , rout_l_36 , rout_l_37 , rout_l_38 , rout_l_39
                , rout_l_40 , rout_l_41 , rout_l_42 , rout_l_43 , rout_l_44 , rout_l_45 , rout_l_46 , rout_l_47 , rout_l_48 , rout_l_49
                , rout_l_50 , rout_l_51 , rout_l_52 , rout_l_53 , rout_l_54 , rout_l_55 , rout_l_56 , rout_l_57 , rout_l_58 , rout_l_59
                , rout_l_60 , rout_l_61 , rout_l_62 , rout_l_63
				};

//
// LUT
// ------------------------------------------------------------

wire [31:0] result_lut;

// Lut function instance from external/xcrypto/rtl
b_lut i_b_lut (
.crs1  (rs1         ), // Source register 1 (LUT input)
.crs2  (rs2         ), // Source register 2 (LUT bottom half)
.crs3  (rs3         ), // Source register 3 (LUT top half)
.result(result_lut  )  //
);

//
// BOP
// ------------------------------------------------------------

wire [31:0] result_bop  ;

b_bop i_b_bop(
.rs1   (rs1         ),
.rs2   (rs2         ),
.rd    (rs3         ),
.lut   (bop_lut     ),
.result(result_bop  )
);


//
// Result multiplexing
// ------------------------------------------------------------

wire result_fsl     = uop_fsl || uop_fsr;

assign result =
    {64{result_fsl}} & {32'b0, r_out[63:32]} |
    {64{uop_mror  }} & {       r_out       } |
    {64{uop_cmov  }} & {32'b0, result_cmov } |
    {64{uop_bop   }} & {32'b0, result_bop  } |
    {64{uop_lut   }} & {32'b0, result_lut  } ;

// Single cycle implementation.
assign ready = valid;

endmodule

`endif