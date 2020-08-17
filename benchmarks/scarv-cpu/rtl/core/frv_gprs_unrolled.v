
//
// module: frv_gprs
//
//  General purpose registers
//

`ifndef FRV_GPRS_DEFINED
`define FRV_GPRS_DEFINED

module frv_gprs (

input  wire         g_clk   , //
input  wire         g_resetn, //

input  wire [ 4:0]  rs1_addr, // Source register 1 address
output wire [31:0]  rs1_data, // Source register 1 read data

input  wire [ 4:0]  rs2_addr, // Source register 2 address
output wire [31:0]  rs2_data, // Source register 2 read data

input  wire [ 4:0]  rs3_addr, // Source register 3 address
output wire [31:0]  rs3_data, // Source register 3 read data

input  wire        rd_wen    , // Destination write enable
input  wire        rd_wide   , // Destination wide write
input  wire [ 4:0] rd_addr   , // Destination address
input  wire [31:0] rd_wdata  , // Destination write data [31:0]
input  wire [31:0] rd_wdata_hi  // Destination write data [63:32]

);

// Use an FPGA BRAM style register file.
parameter BRAM_REGFILE = 0;

reg [31:0] gprs_even [15:0];
reg [31:0] gprs_odd  [15:0];

// Used for debugging.
wire [31:0] gprs      [31:0];

assign rs1_data = gprs[rs1_addr];
assign rs2_data = gprs[rs2_addr];
assign rs3_data = gprs[rs3_addr];

wire        rd_odd       =  rd_addr[0];
wire        rd_even      = !rd_addr[0];

wire [ 3:0] rd_top       =  rd_addr[4:1];

wire        rd_wen_even  = rd_even && rd_wen;
wire        rd_wen_odd   = (rd_odd || rd_wide) && rd_wen;

wire [31:0] rd_wdata_odd = rd_wide ? rd_wdata_hi : rd_wdata;


assign gprs_0  = 32'b0;
assign gprs_1  =  gprs_odd[ 0] ;
assign gprs_2  = gprs_even[ 1] ;
assign gprs_3   = gprs_odd[ 1] ;
assign gprs_4  = gprs_even[ 2] ;
assign gprs_5   = gprs_odd[ 2]  ;
assign gprs_6  = gprs_even[ 3] ;
assign gprs_7   = gprs_odd[ 3]  ;
assign gprs_8  = gprs_even[ 4] ;
assign gprs_9   = gprs_odd[ 4]  ;
assign gprs_10 = gprs_even[ 5] ;
assign gprs_11  = gprs_odd[ 5]  ;
assign gprs_12 = gprs_even[ 6] ;
assign gprs_13  = gprs_odd[ 6]  ;
assign gprs_14 = gprs_even[ 7] ;
assign gprs_15  = gprs_odd[ 7]  ;
assign gprs_16 = gprs_even[ 8] ;
assign gprs_17  = gprs_odd[ 8]  ;
assign gprs_18 = gprs_even[ 9] ;
assign gprs_19  = gprs_odd[ 9]  ;
assign gprs_20 = gprs_even[10] ;
assign gprs_21  = gprs_odd[10]  ;
assign gprs_22 = gprs_even[11]  ;
assign gprs_23  = gprs_odd[11]   ;
assign gprs_24 = gprs_even[12]  ;
assign gprs_25  = gprs_odd[12]   ;
assign gprs_26 = gprs_even[13]  ;
assign gprs_27  = gprs_odd[13]   ;
assign gprs_28 = gprs_even[14]  ;
assign gprs_29  = gprs_odd[14]   ;
assign gprs_30 = gprs_even[15]  ;
assign gprs_31  = gprs_odd[15]   ;


always @(*)
	gprs = { gprs_0 , gprs_1 , gprs_2 , gprs_3 , gprs_4 , gprs_5 , gprs_6 , gprs_7 , gprs_8 , gprs_9
           , gprs_10 , gprs_11 , gprs_12 , gprs_13 , gprs_14 , gprs_15 , gprs_16 , gprs_17 , gprs_18 , gprs_19
           , gprs_20 , gprs_21 , gprs_22 , gprs_23 , gprs_24 , gprs_25 , gprs_26 , gprs_27 , gprs_28 , gprs_29
           , gprs_30 , gprs_31
		   };


always @(posedge g_clk) begin
	                                gprs_even[ 0] <= rd_wdata;
	if(rd_wen_even && rd_top ==  1) gprs_even[ 1] <= rd_wdata;
	if(rd_wen_even && rd_top ==  2) gprs_even[ 2] <= rd_wdata;
	if(rd_wen_even && rd_top ==  3) gprs_even[ 3] <= rd_wdata;
	if(rd_wen_even && rd_top ==  4) gprs_even[ 4] <= rd_wdata;
	if(rd_wen_even && rd_top ==  5) gprs_even[ 5] <= rd_wdata;
	if(rd_wen_even && rd_top ==  6) gprs_even[ 6] <= rd_wdata;
	if(rd_wen_even && rd_top ==  7) gprs_even[ 7] <= rd_wdata;
	if(rd_wen_even && rd_top ==  8) gprs_even[ 8] <= rd_wdata;
	if(rd_wen_even && rd_top ==  9) gprs_even[ 9] <= rd_wdata;
	if(rd_wen_even && rd_top == 10) gprs_even[10] <= rd_wdata;
	if(rd_wen_even && rd_top == 11) gprs_even[11] <= rd_wdata;
	if(rd_wen_even && rd_top == 12) gprs_even[12] <= rd_wdata;
	if(rd_wen_even && rd_top == 13) gprs_even[13] <= rd_wdata;
	if(rd_wen_even && rd_top == 14) gprs_even[14] <= rd_wdata;
	if(rd_wen_even && rd_top == 15) gprs_even[15] <= rd_wdata;
end


always @(posedge g_clk) begin
	if(rd_wen_odd && rd_top ==  0) gprs_odd[ 0] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top ==  1) gprs_odd[ 1] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top ==  2) gprs_odd[ 2] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top ==  3) gprs_odd[ 3] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top ==  4) gprs_odd[ 4] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top ==  5) gprs_odd[ 5] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top ==  6) gprs_odd[ 6] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top ==  7) gprs_odd[ 7] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top ==  8) gprs_odd[ 8] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top ==  9) gprs_odd[ 9] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top == 10) gprs_odd[10] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top == 11) gprs_odd[11] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top == 12) gprs_odd[12] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top == 13) gprs_odd[13] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top == 14) gprs_odd[14] <= rd_wdata_odd;
	if(rd_wen_odd && rd_top == 15) gprs_odd[15] <= rd_wdata_odd;
end

endmodule

`endif