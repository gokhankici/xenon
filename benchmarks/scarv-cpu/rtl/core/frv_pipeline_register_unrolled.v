
//
// module: frv_pipeline_register
//
//  Represents a single pipeline stage register in the CPU core.
//

`ifndef  FRV_PIPELINE_REGISTER_DEFINED
`define  FRV_PIPELINE_REGISTER_DEFINED

module frv_pipeline_register (

input  wire             g_clk    , // global clock
input  wire             g_resetn , // synchronous reset

input  wire [ RLEN-1:0] i_data   , // Input data from stage N
input  wire             i_valid  , // Input data valid?
output wire             o_busy   , // Stage N+1 ready to continue?

output wire [ RLEN-1:0] mr_data  , // Most recent data into the stage.

input  wire             flush    , // Flush the contents of the pipeline
input  wire [ RLEN-1:0] flush_dat, // Data to flush *into* the pipeline.

output reg  [ RLEN-1:0] o_data   , // Output data for stage N+1
output wire             o_valid  , // Input data from stage N valid?
input  wire             i_busy     // Stage N+1 ready to continue?

);

parameter RLEN             = 8; // Width of the pipeline register.
parameter BUFFER_HANDSHAKE = 0; // Implement buffered handshake protocol?

assign o_busy  = i_busy ;
assign o_valid = i_valid;

assign mr_data = o_data ;

wire   progress= i_valid && !i_busy;

always @(posedge g_clk) begin
	if(!g_resetn) begin
		o_data <= {RLEN{1'b0}};
	end else if(flush) begin
		o_data <= flush_dat;
	end else if(progress) begin
		o_data <= i_data;
	end
end

endmodule

`endif
