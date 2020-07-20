
//
// module: b_bop
//
//  Implements the ternary bitwise `bop` instruction
//
module b_bop (

input  wire [31:0] rd       ,
input  wire [31:0] rs1      ,
input  wire [31:0] rs2      ,
input  wire [ 7:0] lut      ,

output wire [31:0] result    

);

wire idx_0  = { rd[0], rs2[0], rs1[0] };
wire idx_1  = { rd[1], rs2[1], rs1[1] };
wire idx_2  = { rd[2], rs2[2], rs1[2] };
wire idx_3  = { rd[3], rs2[3], rs1[3] };
wire idx_4  = { rd[4], rs2[4], rs1[4] };
wire idx_5  = { rd[5], rs2[5], rs1[5] };
wire idx_6  = { rd[6], rs2[6], rs1[6] };
wire idx_7  = { rd[7], rs2[7], rs1[7] };
wire idx_8  = { rd[8], rs2[8], rs1[8] };
wire idx_9  = { rd[9], rs2[9], rs1[9] };
wire idx_10 = { rd[10], rs2[10], rs1[10] };
wire idx_11 = { rd[11], rs2[11], rs1[11] };
wire idx_12 = { rd[12], rs2[12], rs1[12] };
wire idx_13 = { rd[13], rs2[13], rs1[13] };
wire idx_14 = { rd[14], rs2[14], rs1[14] };
wire idx_15 = { rd[15], rs2[15], rs1[15] };
wire idx_16 = { rd[16], rs2[16], rs1[16] };
wire idx_17 = { rd[17], rs2[17], rs1[17] };
wire idx_18 = { rd[18], rs2[18], rs1[18] };
wire idx_19 = { rd[19], rs2[19], rs1[19] };
wire idx_20 = { rd[20], rs2[20], rs1[20] };
wire idx_21 = { rd[21], rs2[21], rs1[21] };
wire idx_22 = { rd[22], rs2[22], rs1[22] };
wire idx_23 = { rd[23], rs2[23], rs1[23] };
wire idx_24 = { rd[24], rs2[24], rs1[24] };
wire idx_25 = { rd[25], rs2[25], rs1[25] };
wire idx_26 = { rd[26], rs2[26], rs1[26] };
wire idx_27 = { rd[27], rs2[27], rs1[27] };
wire idx_28 = { rd[28], rs2[28], rs1[28] };
wire idx_29 = { rd[29], rs2[29], rs1[29] };
wire idx_30 = { rd[30], rs2[30], rs1[30] };
wire idx_31 = { rd[31], rs2[31], rs1[31] };

assign result = { lut[idx_0]
                , lut[idx_1]
                , lut[idx_2]
                , lut[idx_3]
                , lut[idx_4]
                , lut[idx_5]
                , lut[idx_6]
                , lut[idx_7]
                , lut[idx_8]
                , lut[idx_9]
                , lut[idx_10]
                , lut[idx_11]
                , lut[idx_12]
                , lut[idx_13]
                , lut[idx_14]
                , lut[idx_15]
                , lut[idx_16]
                , lut[idx_17]
                , lut[idx_18]
                , lut[idx_19]
                , lut[idx_20]
                , lut[idx_21]
                , lut[idx_22]
                , lut[idx_23]
                , lut[idx_24]
                , lut[idx_25]
                , lut[idx_26]
                , lut[idx_27]
                , lut[idx_28]
                , lut[idx_29]
                , lut[idx_30]
                , lut[idx_31]
				};

reg [31:0] result_r;
assign result_r = result;

endmodule
