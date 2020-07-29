module test(clk, cond, x, y, z, out);

	input wire clk, x, y, z, cond;
	output reg out;

	reg x1, y1, z1, tmp1, tmp2;

	add3 ADD3(x1, y1, z1, tmp1);

	assign tmp2 = x1 + y1 + z1;

	always @(posedge clk) begin
		x1 <= x;
		y1 <= y;
		z1 <= z;

		if (cond)
			out <= tmp1;
		else
			out <= tmp2;
	end

endmodule // test

// -----------------------------------------------------------------------------

module add3(x, y, z, r);

	input  wire x, y, z;
	output wire r;

	wire tmp;

	add ADD1(x, y, tmp);
	add ADD2(tmp, z, r);

endmodule

// -----------------------------------------------------------------------------

module add(x, y, r);

	input  wire x, y;
	output wire r;

	assign r = x + y;

endmodule

