
//
// module: b_lut
//
//  Implements the core logic for the xc.lut instruction.
//

`ifndef B_LUT_DEFINED
`define B_LUT_DEFINED

module b_lut (

input  wire [31:0] crs1  , // Source register 1 (LUT input)
input  wire [31:0] crs2  , // Source register 2 (LUT bottom half)
input  wire [31:0] crs3  , // Source register 3 (LUT top half)

output wire [31:0] result  //

);

wire [ 3:0] lut_arr [15:0];
wire [63:0] lut_con = {crs1, crs2};

assign lut_arr = { lut_con[4*0 +3:4*0 ]
                 , lut_con[4*1 +3:4*1 ]
                 , lut_con[4*2 +3:4*2 ]
                 , lut_con[4*3 +3:4*3 ]
                 , lut_con[4*4 +3:4*4 ]
                 , lut_con[4*5 +3:4*5 ]
                 , lut_con[4*6 +3:4*6 ]
                 , lut_con[4*7 +3:4*7 ]
                 , lut_con[4*8 +3:4*8 ]
                 , lut_con[4*9 +3:4*9 ]
                 , lut_con[4*10+3:4*10]
                 , lut_con[4*11+3:4*11]
                 , lut_con[4*12+3:4*12]
                 , lut_con[4*13+3:4*13]
                 , lut_con[4*14+3:4*14]
                 , lut_con[4*15+3:4*15]
                 };

assign result = { lut_arr[crs3[4*0+3:4*0]]
                , lut_arr[crs3[4*1+3:4*1]]
                , lut_arr[crs3[4*2+3:4*2]]
                , lut_arr[crs3[4*3+3:4*3]]
                , lut_arr[crs3[4*4+3:4*4]]
                , lut_arr[crs3[4*5+3:4*5]]
                , lut_arr[crs3[4*6+3:4*6]]
                , lut_arr[crs3[4*7+3:4*7]]
                };

reg [31:0] result_r;
assign result_r = result;

endmodule

`endif