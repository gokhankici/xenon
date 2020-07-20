
//
// module: p_addsub
//
//  Implemented packed addition/subtraction for 32-bit 2s complement values.
//
module p_addsub (

input  wire [31:0]  lhs             , // Left hand input
input  wire [31:0]  rhs             , // Right hand input.

input  wire [ 4:0]  pw              , // Pack width to operate on
input  wire [ 0:0]  cin             , // Carry in bit.
input  wire [ 0:0]  sub             , // Subtract if set, else add.

input  wire         c_en            , // Carry enable bits.
output wire [32:0]  c_out           , // Carry bits
output wire [31:0]  result            // Result of the operation

);

//
// One-hot pack width wires
wire pw_32 = pw[0];
wire pw_16 = pw[1];
wire pw_8  = pw[2];
wire pw_4  = pw[3];
wire pw_2  = pw[4];

// Carry bit masks
(*keep*)
    /* verilator lint_off UNOPTFLAT */
wire [31:0] carry_mask;
wire [32:0] carry_chain;
/* verilator lint_on UNOPTFLAT */

// Carry in IFF subtracting or forcing a carry in.

// Invert RHS iff subtracting.
wire [31:0] rhs_m          = sub ? ~rhs : rhs;

//
// Generate the carry mask bits.
	assign carry_mask_0  = c_en && 1'b1;
	assign carry_mask_1  = c_en && !pw_2;
	assign carry_mask_2  = c_en && 1'b1;
	assign carry_mask_3  = c_en && !pw_2 && !pw_4;
	assign carry_mask_4  = c_en && 1'b1;
	assign carry_mask_5  = c_en && !pw_2;
	assign carry_mask_6  = c_en && 1'b1;
	assign carry_mask_7  = c_en && !pw_2 && !pw_4 && !pw_8;
	assign carry_mask_8  = c_en && 1'b1;
	assign carry_mask_9  = c_en && !pw_2;
	assign carry_mask_10 = c_en && 1'b1;
	assign carry_mask_11 = c_en && !pw_2 && !pw_4;
	assign carry_mask_12 = c_en && 1'b1;
	assign carry_mask_13 = c_en && !pw_2;
	assign carry_mask_14 = c_en && 1'b1;
	assign carry_mask_15 = c_en && !pw_2 && !pw_4 && !pw_8 && !pw_16;
	assign carry_mask_16 = c_en && 1'b1;
	assign carry_mask_17 = c_en && !pw_2;
	assign carry_mask_18 = c_en && 1'b1;
	assign carry_mask_19 = c_en && !pw_2 && !pw_4;
	assign carry_mask_20 = c_en && 1'b1;
	assign carry_mask_21 = c_en && !pw_2;
	assign carry_mask_22 = c_en && 1'b1;
	assign carry_mask_23 = c_en && !pw_2 && !pw_4 && !pw_8;
	assign carry_mask_24 = c_en && 1'b1;
	assign carry_mask_25 = c_en && !pw_2;
	assign carry_mask_26 = c_en && 1'b1;
	assign carry_mask_27 = c_en && !pw_2 && !pw_4;
	assign carry_mask_28 = c_en && 1'b1;
	assign carry_mask_29 = c_en && !pw_2;
	assign carry_mask_30 = c_en && 1'b1;
	assign carry_mask_31 = c_en && !pw_2 && !pw_4 && !pw_8 && !pw_16;

    assign   carry_0     = (lhs[0 ] && rhs_m[0 ]) || (c_in_0  && (lhs[0 ]^rhs_m[0 ]));
    assign   carry_1     = (lhs[1 ] && rhs_m[1 ]) || (c_in_1  && (lhs[1 ]^rhs_m[1 ]));
    assign   carry_2     = (lhs[2 ] && rhs_m[2 ]) || (c_in_2  && (lhs[2 ]^rhs_m[2 ]));
    assign   carry_3     = (lhs[3 ] && rhs_m[3 ]) || (c_in_3  && (lhs[3 ]^rhs_m[3 ]));
    assign   carry_4     = (lhs[4 ] && rhs_m[4 ]) || (c_in_4  && (lhs[4 ]^rhs_m[4 ]));
    assign   carry_5     = (lhs[5 ] && rhs_m[5 ]) || (c_in_5  && (lhs[5 ]^rhs_m[5 ]));
    assign   carry_6     = (lhs[6 ] && rhs_m[6 ]) || (c_in_6  && (lhs[6 ]^rhs_m[6 ]));
    assign   carry_7     = (lhs[7 ] && rhs_m[7 ]) || (c_in_7  && (lhs[7 ]^rhs_m[7 ]));
    assign   carry_8     = (lhs[8 ] && rhs_m[8 ]) || (c_in_8  && (lhs[8 ]^rhs_m[8 ]));
    assign   carry_9     = (lhs[9 ] && rhs_m[9 ]) || (c_in_9  && (lhs[9 ]^rhs_m[9 ]));
    assign   carry_10    = (lhs[10] && rhs_m[10]) || (c_in_10 && (lhs[10]^rhs_m[10]));
    assign   carry_11    = (lhs[11] && rhs_m[11]) || (c_in_11 && (lhs[11]^rhs_m[11]));
    assign   carry_12    = (lhs[12] && rhs_m[12]) || (c_in_12 && (lhs[12]^rhs_m[12]));
    assign   carry_13    = (lhs[13] && rhs_m[13]) || (c_in_13 && (lhs[13]^rhs_m[13]));
    assign   carry_14    = (lhs[14] && rhs_m[14]) || (c_in_14 && (lhs[14]^rhs_m[14]));
    assign   carry_15    = (lhs[15] && rhs_m[15]) || (c_in_15 && (lhs[15]^rhs_m[15]));
    assign   carry_16    = (lhs[16] && rhs_m[16]) || (c_in_16 && (lhs[16]^rhs_m[16]));
    assign   carry_17    = (lhs[17] && rhs_m[17]) || (c_in_17 && (lhs[17]^rhs_m[17]));
    assign   carry_18    = (lhs[18] && rhs_m[18]) || (c_in_18 && (lhs[18]^rhs_m[18]));
    assign   carry_19    = (lhs[19] && rhs_m[19]) || (c_in_19 && (lhs[19]^rhs_m[19]));
    assign   carry_20    = (lhs[20] && rhs_m[20]) || (c_in_20 && (lhs[20]^rhs_m[20]));
    assign   carry_21    = (lhs[21] && rhs_m[21]) || (c_in_21 && (lhs[21]^rhs_m[21]));
    assign   carry_22    = (lhs[22] && rhs_m[22]) || (c_in_22 && (lhs[22]^rhs_m[22]));
    assign   carry_23    = (lhs[23] && rhs_m[23]) || (c_in_23 && (lhs[23]^rhs_m[23]));
    assign   carry_24    = (lhs[24] && rhs_m[24]) || (c_in_24 && (lhs[24]^rhs_m[24]));
    assign   carry_25    = (lhs[25] && rhs_m[25]) || (c_in_25 && (lhs[25]^rhs_m[25]));
    assign   carry_26    = (lhs[26] && rhs_m[26]) || (c_in_26 && (lhs[26]^rhs_m[26]));
    assign   carry_27    = (lhs[27] && rhs_m[27]) || (c_in_27 && (lhs[27]^rhs_m[27]));
    assign   carry_28    = (lhs[28] && rhs_m[28]) || (c_in_28 && (lhs[28]^rhs_m[28]));
    assign   carry_29    = (lhs[29] && rhs_m[29]) || (c_in_29 && (lhs[29]^rhs_m[29]));
    assign   carry_30    = (lhs[30] && rhs_m[30]) || (c_in_30 && (lhs[30]^rhs_m[30]));
    assign   carry_31    = (lhs[31] && rhs_m[31]) || (c_in_31 && (lhs[31]^rhs_m[31]));

    assign c_out = { carry_0 
	               , carry_1 
	               , carry_2 
	               , carry_3 
	               , carry_4 
	               , carry_5 
	               , carry_6 
	               , carry_7 
	               , carry_8 
	               , carry_9 
	               , carry_10
	               , carry_11
	               , carry_12
	               , carry_13
	               , carry_14
	               , carry_15
	               , carry_16
	               , carry_17
	               , carry_18
	               , carry_19
	               , carry_20
	               , carry_21
	               , carry_22
	               , carry_23
	               , carry_24
	               , carry_25
	               , carry_26
	               , carry_27
	               , carry_28
	               , carry_29
	               , carry_30
	               , carry_31
                   , ((carry_31 && carry_mask[31]) || force_carry_31)
				   };
    
    assign   force_carry_0  = 0;
    assign   force_carry_1  = sub && (pw_2);
    assign   force_carry_2  = 0;
    assign   force_carry_3  = sub && (pw_2 || pw_4);
    assign   force_carry_4  = 0;
    assign   force_carry_5  = sub && (pw_2);
    assign   force_carry_6  = 0;
    assign   force_carry_7  = sub && (pw_2 || pw_4 || pw_8);
    assign   force_carry_8  = 0;
    assign   force_carry_9  = sub && (pw_2);
    assign   force_carry_10 = 0;
    assign   force_carry_11 = sub && (pw_2 || pw_4);
    assign   force_carry_12 = 0;
    assign   force_carry_13 = sub && (pw_2);
    assign   force_carry_14 = 0;
    assign   force_carry_15 = sub && (pw_16 || pw_2 || pw_4 || pw_8);
    assign   force_carry_16 = 0;
    assign   force_carry_17 = sub && (pw_2);
    assign   force_carry_18 = 0;
    assign   force_carry_19 = sub && (pw_2 || pw_4);
    assign   force_carry_20 = 0;
    assign   force_carry_21 = sub && (pw_2);
    assign   force_carry_22 = 0;
    assign   force_carry_23 = sub && (pw_2 || pw_4 || pw_8);
    assign   force_carry_24 = 0;
    assign   force_carry_25 = sub && (pw_2);
    assign   force_carry_26 = 0;
    assign   force_carry_27 = sub && (pw_2 || pw_4);
    assign   force_carry_28 = 0;
    assign   force_carry_29 = sub && (pw_2);
    assign   force_carry_30 = 0;
    assign   force_carry_31 = 0;

    assign   c_in_0      = sub || cin;
    assign   c_in_1      = (carry_0  && carry_mask_0 ) || force_carry_0 ;
    assign   c_in_2      = (carry_1  && carry_mask_1 ) || force_carry_1 ;
    assign   c_in_3      = (carry_2  && carry_mask_2 ) || force_carry_2 ;
    assign   c_in_4      = (carry_3  && carry_mask_3 ) || force_carry_3 ;
    assign   c_in_5      = (carry_4  && carry_mask_4 ) || force_carry_4 ;
    assign   c_in_6      = (carry_5  && carry_mask_5 ) || force_carry_5 ;
    assign   c_in_7      = (carry_6  && carry_mask_6 ) || force_carry_6 ;
    assign   c_in_8      = (carry_7  && carry_mask_7 ) || force_carry_7 ;
    assign   c_in_9      = (carry_8  && carry_mask_8 ) || force_carry_8 ;
    assign   c_in_10     = (carry_9  && carry_mask_9 ) || force_carry_9 ;
    assign   c_in_11     = (carry_10 && carry_mask_10) || force_carry_10;
    assign   c_in_12     = (carry_11 && carry_mask_11) || force_carry_11;
    assign   c_in_13     = (carry_12 && carry_mask_12) || force_carry_12;
    assign   c_in_14     = (carry_13 && carry_mask_13) || force_carry_13;
    assign   c_in_15     = (carry_14 && carry_mask_14) || force_carry_14;
    assign   c_in_16     = (carry_15 && carry_mask_15) || force_carry_15;
    assign   c_in_17     = (carry_16 && carry_mask_16) || force_carry_16;
    assign   c_in_18     = (carry_17 && carry_mask_17) || force_carry_17;
    assign   c_in_19     = (carry_18 && carry_mask_18) || force_carry_18;
    assign   c_in_20     = (carry_19 && carry_mask_19) || force_carry_19;
    assign   c_in_21     = (carry_20 && carry_mask_20) || force_carry_20;
    assign   c_in_22     = (carry_21 && carry_mask_21) || force_carry_21;
    assign   c_in_23     = (carry_22 && carry_mask_22) || force_carry_22;
    assign   c_in_24     = (carry_23 && carry_mask_23) || force_carry_23;
    assign   c_in_25     = (carry_24 && carry_mask_24) || force_carry_24;
    assign   c_in_26     = (carry_25 && carry_mask_25) || force_carry_25;
    assign   c_in_27     = (carry_26 && carry_mask_26) || force_carry_26;
    assign   c_in_28     = (carry_27 && carry_mask_27) || force_carry_27;
    assign   c_in_29     = (carry_28 && carry_mask_28) || force_carry_28;
    assign   c_in_30     = (carry_29 && carry_mask_29) || force_carry_29;
    assign   c_in_31     = (carry_30 && carry_mask_30) || force_carry_30;

    assign carry_chain = { sub || cin
                         , (carry_0  && carry_mask_0 ) || force_carry_0 
                         , (carry_1  && carry_mask_1 ) || force_carry_1 
                         , (carry_2  && carry_mask_2 ) || force_carry_2 
                         , (carry_3  && carry_mask_3 ) || force_carry_3 
                         , (carry_4  && carry_mask_4 ) || force_carry_4 
                         , (carry_5  && carry_mask_5 ) || force_carry_5 
                         , (carry_6  && carry_mask_6 ) || force_carry_6 
                         , (carry_7  && carry_mask_7 ) || force_carry_7 
                         , (carry_8  && carry_mask_8 ) || force_carry_8 
                         , (carry_9  && carry_mask_9 ) || force_carry_9 
                         , (carry_10 && carry_mask_10) || force_carry_10
                         , (carry_11 && carry_mask_11) || force_carry_11
                         , (carry_12 && carry_mask_12) || force_carry_12
                         , (carry_13 && carry_mask_13) || force_carry_13
                         , (carry_14 && carry_mask_14) || force_carry_14
                         , (carry_15 && carry_mask_15) || force_carry_15
                         , (carry_16 && carry_mask_16) || force_carry_16
                         , (carry_17 && carry_mask_17) || force_carry_17
                         , (carry_18 && carry_mask_18) || force_carry_18
                         , (carry_19 && carry_mask_19) || force_carry_19
                         , (carry_20 && carry_mask_20) || force_carry_20
                         , (carry_21 && carry_mask_21) || force_carry_21
                         , (carry_22 && carry_mask_22) || force_carry_22
                         , (carry_23 && carry_mask_23) || force_carry_23
                         , (carry_24 && carry_mask_24) || force_carry_24
                         , (carry_25 && carry_mask_25) || force_carry_25
                         , (carry_26 && carry_mask_26) || force_carry_26
                         , (carry_27 && carry_mask_27) || force_carry_27
                         , (carry_28 && carry_mask_28) || force_carry_28
                         , (carry_29 && carry_mask_29) || force_carry_29
                         , (carry_30 && carry_mask_30) || force_carry_30
                         , (carry_31 && carry_mask_31) || force_carry_31
					     };
                         
    assign result = { lhs[0 ] ^ rhs_m[0 ] ^ c_in_0 
                    , lhs[1 ] ^ rhs_m[1 ] ^ c_in_1 
                    , lhs[2 ] ^ rhs_m[2 ] ^ c_in_2 
                    , lhs[3 ] ^ rhs_m[3 ] ^ c_in_3 
                    , lhs[4 ] ^ rhs_m[4 ] ^ c_in_4 
                    , lhs[5 ] ^ rhs_m[5 ] ^ c_in_5 
                    , lhs[6 ] ^ rhs_m[6 ] ^ c_in_6 
                    , lhs[7 ] ^ rhs_m[7 ] ^ c_in_7 
                    , lhs[8 ] ^ rhs_m[8 ] ^ c_in_8 
                    , lhs[9 ] ^ rhs_m[9 ] ^ c_in_9 
                    , lhs[10] ^ rhs_m[10] ^ c_in_10
                    , lhs[11] ^ rhs_m[11] ^ c_in_11
                    , lhs[12] ^ rhs_m[12] ^ c_in_12
                    , lhs[13] ^ rhs_m[13] ^ c_in_13
                    , lhs[14] ^ rhs_m[14] ^ c_in_14
                    , lhs[15] ^ rhs_m[15] ^ c_in_15
                    , lhs[16] ^ rhs_m[16] ^ c_in_16
                    , lhs[17] ^ rhs_m[17] ^ c_in_17
                    , lhs[18] ^ rhs_m[18] ^ c_in_18
                    , lhs[19] ^ rhs_m[19] ^ c_in_19
                    , lhs[20] ^ rhs_m[20] ^ c_in_20
                    , lhs[21] ^ rhs_m[21] ^ c_in_21
                    , lhs[22] ^ rhs_m[22] ^ c_in_22
                    , lhs[23] ^ rhs_m[23] ^ c_in_23
                    , lhs[24] ^ rhs_m[24] ^ c_in_24
                    , lhs[25] ^ rhs_m[25] ^ c_in_25
                    , lhs[26] ^ rhs_m[26] ^ c_in_26
                    , lhs[27] ^ rhs_m[27] ^ c_in_27
                    , lhs[28] ^ rhs_m[28] ^ c_in_28
                    , lhs[29] ^ rhs_m[29] ^ c_in_29
                    , lhs[30] ^ rhs_m[30] ^ c_in_30
                    , lhs[31] ^ rhs_m[31] ^ c_in_31
					};

	reg [32:0]  c_out_r;
	reg [31:0]  result_r;

	always @(*) begin
		c_out_r = c_out;
		result_r = result;
	end

endmodule
