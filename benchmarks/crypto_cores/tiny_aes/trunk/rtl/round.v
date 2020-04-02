/*
 * Copyright 2012, Homer Hsing <homer.hsing@gmail.com>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/* one AES round for every two clock cycles */
module one_round (clk, state_in, key, state_out);
    input              clk;
    input      [127:0] state_in, key;
    output reg [127:0] state_out;
    wire       [31:0]  s0,  s1,  s2,  s3,
                       z0,  z1,  z2,  z3,
                       p00, p01, p02, p03,
                       p10, p11, p12, p13,
                       p20, p21, p22, p23,
                       p30, p31, p32, p33,
                       k0,  k1,  k2,  k3;

    // REWRITE
    // assign {k0, k1, k2, k3} = key;
    assign k0 = key[127: 96];
    assign k1 = key[ 95: 64];
    assign k2 = key[ 63: 32];
    assign k3 = key[ 31:  0];

    // REWRITE
    // assign {s0, s1, s2, s3} = state_in;
    assign s0 = state_in[127: 96];
    assign s1 = state_in[ 95: 64];
    assign s2 = state_in[ 63: 32];
    assign s3 = state_in[ 31:  0];

    table_lookup
        t0 (clk, s0, p00, p01, p02, p03),
        t1 (clk, s1, p10, p11, p12, p13),
        t2 (clk, s2, p20, p21, p22, p23),
        t3 (clk, s3, p30, p31, p32, p33);

    assign z0 = p00 ^ p11 ^ p22 ^ p33 ^ k0;
    assign z1 = p03 ^ p10 ^ p21 ^ p32 ^ k1;
    assign z2 = p02 ^ p13 ^ p20 ^ p31 ^ k2;
    assign z3 = p01 ^ p12 ^ p23 ^ p30 ^ k3;

    always @ (posedge clk)
        state_out <= {z0, z1, z2, z3};
endmodule

/* AES final round for every two clock cycles */
module final_round (clk, state_in, key_in, state_out);
    input              clk;
    input      [127:0] state_in;
    input      [127:0] key_in;
    output reg [127:0] state_out;
    wire [31:0] s0,  s1,  s2,  s3,
                z0,  z1,  z2,  z3,
                k0,  k1,  k2,  k3;
    wire [7:0]  p00, p01, p02, p03,
                p10, p11, p12, p13,
                p20, p21, p22, p23,
                p30, p31, p32, p33;
    
    // REWRITE
    // assign {k0, k1, k2, k3} = key_in;
    assign k0 = key_in[127: 96];
    assign k1 = key_in[ 95: 64];
    assign k2 = key_in[ 63: 32];
    assign k3 = key_in[ 31:  0];
    
    // REWRITE
    // assign {s0, s1, s2, s3} = state_in;
    assign s0 = state_in[127: 96];
    assign s1 = state_in[ 95: 64];
    assign s2 = state_in[ 63: 32];
    assign s3 = state_in[ 31:  0];

	// REWRITE
    // S4
    //     S4_1 (clk, s0, {p00, p01, p02, p03}),
    //     S4_2 (clk, s1, {p10, p11, p12, p13}),
    //     S4_3 (clk, s2, {p20, p21, p22, p23}),
    //     S4_4 (clk, s3, {p30, p31, p32, p33});

	wire [31:0] x,y,z,t;

	assign p00 = x[ 7: 0];
	assign p01 = x[15: 8];
	assign p02 = x[23:16];
	assign p03 = x[31:24];

	assign p10 = y[ 7: 0];
	assign p11 = y[15: 8];
	assign p12 = y[23:16];
	assign p13 = y[31:24];

	assign p20 = z[ 7: 0];
	assign p21 = z[15: 8];
	assign p22 = z[23:16];
	assign p23 = z[31:24];

	assign p30 = t[ 7: 0];
	assign p31 = t[15: 8];
	assign p32 = t[23:16];
	assign p33 = t[31:24];

    S4
        S4_1 (clk, s0, x),
        S4_2 (clk, s1, y),
        S4_3 (clk, s2, z),
        S4_4 (clk, s3, t);

    assign z0 = {p00, p11, p22, p33} ^ k0;
    assign z1 = {p10, p21, p32, p03} ^ k1;
    assign z2 = {p20, p31, p02, p13} ^ k2;
    assign z3 = {p30, p01, p12, p23} ^ k3;

    always @ (posedge clk)
        state_out <= {z0, z1, z2, z3};
endmodule

