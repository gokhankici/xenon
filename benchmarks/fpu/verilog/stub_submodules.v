// `include "pre_norm.v"
module pre_norm(clk,
                rmode, add, opa, opb, opa_nan, opb_nan, // inputs
                fracta_out, fractb_out, exp_dn_out, sign, nan_sign, result_zero_sign, fasu_op // outputs
                );
   input clk, rmode, add, opa, opb, opa_nan, opb_nan;
   output reg	[26:0]	fracta_out, fractb_out;
   output reg [7:0]    exp_dn_out;
   output reg          sign;
   output reg          nan_sign;
   output reg          result_zero_sign;
   output reg          fasu_op;

   always @(posedge clk) begin
      fracta_out <= 0;
      fractb_out <= 0;
      exp_dn_out <= 0;
      sign <= 0;
      nan_sign <= 0;
      result_zero_sign <= 0;
      fasu_op <= 0;
   end
endmodule


// `include "pre_norm_fmul.v"
module pre_norm_fmul(clk,
                     fpu_op, opa, opb,
                     fracta, fractb, exp_out, sign, sign_exe, inf, exp_ovf, underflow
                     );
   input clk, fpu_op, opa, opb;
   output wire [23:0] fracta, fractb;
   output reg [7:0]   exp_out;
   output reg         sign;
   output reg         sign_exe;
   output reg         inf;
   output reg [1:0]   exp_ovf;
   output reg [2:0]   underflow;

   assign fracta = 0;
   assign fractb = 0;

   always @(posedge clk) begin
      exp_out <= 0;
      sign <= 0;
      sign_exe <= 0;
      inf <= 0;
      exp_ovf <= 0;
      underflow <= 0;
   end
endmodule


// `include "primitives.v"
module add_sub27(add, opa, opb,
                 sum, co
                 );
   input add, opa, opb;
   output [26:0] sum;
   output        co;

   assign sum = 0;
   assign co = 0;
endmodule

module mul_r2(clk,
              opa, opb,
              prod
              );
   input clk, opa, opb;
   output reg [47:0] prod;

   always @(posedge clk) begin
      prod <= 0;
   end
endmodule

module div_r2(clk,
              opa, opb,
              quo, rem
              );
   input clk, opa, opb;
   output reg [49:0] quo, rem;

   always @(posedge clk) begin
      quo <= 0;
      rem <= 0;
   end
endmodule

// `include "post_norm.v"
module post_norm(clk,
                 fpu_op, opas, sign, rmode, fract_in, exp_in, exp_ovf, opa_dn, opb_dn, rem_00, div_opa_ldz, output_zero, // inputs
                 out, ine, overflow, underflow, f2i_out_sign // outputs
                 );
   input        clk;
   input [2:0]  fpu_op;
   input        opas;
   input        sign;
   input [1:0]  rmode;
   input [47:0] fract_in;
   input [1:0]  exp_ovf;
   input [7:0]  exp_in;
   input        opa_dn, opb_dn;
   input        rem_00;
   input [4:0]  div_opa_ldz;
   input        output_zero;
   output wire [30:0] out;
   output wire        ine;
   output wire        overflow, underflow;
   output wire        f2i_out_sign;

   assign out = 0;
   assign ine = 0;
   assign overflow = 0;
   assign underflow = 0;
   assign f2i_out_sign = 0;
endmodule

// `include "except.v"
module except(clk,
              opa, opb, // inputs
              inf, ind, qnan, snan, opa_nan, opb_nan, opa_00, opb_00, opa_inf, opb_inf, opa_dn, opb_dn //outputs
              );

   input        clk;
   input [31:0] opa, opb;
   output reg   inf, ind, qnan, snan, opa_nan, opb_nan;
   output reg   opa_00, opb_00;
   output reg   opa_inf, opb_inf;
   output reg   opa_dn;
   output reg   opb_dn;

   always @(posedge clk) begin
      inf <= 0;
      ind <= 0;
      qnan <= 0;
      snan <= 0;
      opa_nan <= 0;
      opb_nan <= 0;
      opa_00 <= 0;
      opb_00 <= 0;
      opa_inf <= 0;
      opb_inf <= 0;
      opa_dn <= 0;
      opb_dn <= 0;
   end
endmodule
