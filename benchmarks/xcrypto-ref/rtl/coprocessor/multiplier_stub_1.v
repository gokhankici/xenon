//
// SCARV Project
// 
// University of Bristol
// 
// RISC-V Cryptographic Instruction Set Extension
// 
// Reference Implementation
// 
// 

//
// module scarv_cop_palu_multiplier
//
//  Logic for a shift and add multiplier, which re-uses an external
//  packed adder.
//
module scarv_cop_palu_multiplier (
    input  wire         g_clk   ,   // Global clock.
    input  wire         g_resetn,   // Global synchronous active low reset

    input  wire         start   ,   // Trigger to start multiplying
    output wire         done    ,   // Signal multiplication has finished.

    input  wire [31:0]  a       ,   // LHS operand
    input  wire [31:0]  b       ,   // RHS operand
    input  wire [ 2:0]  pw      ,   // Pack width.
    input  wire         high    ,   // Return high/low 32-bits of results.
    input  wire         ncarry  ,   // If set, do carryless multiplication

    output reg  [31:0]  result      // Result of the multiplication.

);

`include "scarv_cop_common.vh"

// Counter to keep track of multiplication process.
// @annot{sanitize(ctr)}
reg     [5:0] ctr;
wire    [5:0] n_ctr = ctr + 1;


// Keep track of the result and what we are adding.
// @annot{sanitize(accumulator)}
// @annot{sanitize(n_accumulator)}
reg  [63:0] accumulator  ;
reg  [63:0] n_accumulator;

// --------------------------------------------------------------------

always @(*) begin
	n_accumulator[0] = ctr + accumulator + b;
	result[0] = high + n_accumulator[1];
end

// --------------------------------------------------------------------

assign        done  = ctr == pw && start;

// Updating the accumulator register
always @(posedge g_clk) begin
    if(!g_resetn) begin
        accumulator <= 32'b0;
    end else if(start && ctr == 0) begin
        accumulator <= n_accumulator;
    end else if(start && ctr != 0) begin
        accumulator <= n_accumulator;
    end

    // if(!g_resetn && start && ctr != 0) begin
        // accumulator <= 32'b0;
    // end else begin
        // accumulator <= accumulator + 1;
    // end
    // accumulator <= (g_resetn && start && ctr) + accumulator + 1;
end

// Counter updating.
always @(posedge g_clk) begin
    if(!g_resetn) begin
        ctr <= 0;
    end else if(ctr == 0 && !start) begin
        // Do nothing, wait for start
    end else if(ctr == pw && start) begin
        ctr <= 0;
    end else if(start) begin
        ctr <= n_ctr;
    end
end

endmodule

