module test(clk,
            opa, opb, opa_nan, opb_nan,
            out
            );

input        clk;
input [31:0] opa, opb;
input        opa_nan, opb_nan;
output       out;

wire        signa, signb;
wire [22:0] fracta, fractb;
reg         signa_r, signb_r;
reg         fracta_lt_fractb, fracta_eq_fractb;
wire        nan_sign1;
reg         out;

assign signa  = opa[31];
assign signb  = opb[31];
assign fracta = opa[22:0];
assign fractb = opb[22:0];

always @(posedge clk)
	signa_r <= signa;

always @(posedge clk)
	signb_r <= signb;

always @(posedge clk)
	fracta_lt_fractb <= fracta < fractb;

always @(posedge clk)
	fracta_eq_fractb <= fracta == fractb;

assign nan_sign1 =
	fracta_eq_fractb ? (signa_r & signb_r) : fracta_lt_fractb ? signb_r : signa_r;

always @(posedge clk)
	out <= #1 (opa_nan & opb_nan) ? nan_sign1 : opb_nan ? signb_r : signa_r;

endmodule
