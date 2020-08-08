`include "mux2.v"
`include "control_pipeline.v"
`include "rom32.v"

module mips_pipeline(clk, reset);
    input clk, reset;

    reg  [31:0] IF_pc;
    wire [31:0] IF_instr, IF_pc_maybestalled, IF_pc_jump, IF_pc_next, IF_pc4;
    reg         Stall;
    reg  [31:0] ID_instr, ID_pc4;
    wire [5:0]  ID_op;
    wire [4:0]  ID_rs, ID_rt;
    wire [31:0] ID_jaddr;
    wire        ID_RegWrite_v, ID_MemWrite_v, ID_MemRead_v, ID_Branch_v, ID_Jump_v, ID_RegDst, ID_MemtoReg,  ID_ALUSrc;
    wire        ID_MemRead, ID_Jump;
    wire [1:0]  ID_ALUOp;
    reg  [4:0]  EX_rt;
    reg         EX_MemRead;

    always @(posedge clk)
        if (reset)
            IF_pc <= 0;
        else
            // IF_pc <= IF_pc_next;
            IF_pc <= IF_pc4;

    assign IF_pc4 = IF_pc + 32'd4;

    // mux2 #(32) IF_SMUX(Stall, IF_pc4, IF_pc, IF_pc_maybestalled);
    // mux2 #(32) IF_JMPMUX(ID_Jump, IF_pc_maybestalled, ID_jaddr, IF_pc_jump);
    // assign IF_pc_next = IF_pc_jump;

    rom32 IMEM(IF_pc, IF_instr);

    reg IF_instr_tmp;
    always @(*) IF_instr_tmp = IF_instr;

    always @(posedge clk) begin
        if (reset) begin
            ID_instr <= 0;
            // ID_pc4   <= 0;
        end else begin
            // if (ID_Jump)
            if (ID_op)
                ID_instr <= 0;
            else if (Stall)
                ID_instr <= ID_instr;
            else
                ID_instr <= IF_instr_tmp;
            // ID_pc4 <= IF_pc4;
        end
    end

    assign ID_op    = ID_instr[31:26];
    // assign ID_rs    = ID_instr[25:21];
    // assign ID_rt    = ID_instr[20:16];
    // assign ID_jaddr = {ID_pc4[31:28], ID_instr[25:0], 2'b00};

    always @(*) begin
        if (ID_op)
            Stall = 0;
        else
            Stall = 1;
    end

    // control_pipeline CTL(.opcode(ID_op),           .RegDst(ID_RegDst),
    //                      .ALUSrc(ID_ALUSrc),       .MemtoReg(ID_MemtoReg),
    //                      .RegWrite(ID_RegWrite_v), .MemRead(ID_MemRead_v),
    //                      .MemWrite(ID_MemWrite_v), .Branch(ID_Branch_v),
    //                      .ALUOp(ID_ALUOp),         .Jump(ID_Jump_v));

    // mux2 #(1) ID_MR_SMUX(Stall, ID_MemRead_v, 1'b0, ID_MemRead);
    // mux2 #(1) ID_JU_SMUX(Stall, ID_Jump_v,    1'b0, ID_Jump);

    // always @(posedge clk) begin
    //     if (reset) begin
    //         EX_MemRead <= 0;
    //         EX_rt      <= 0;
    //     end else begin
    //         EX_MemRead <= ID_MemRead;
    //         EX_rt      <= ID_rt;
    //     end
    // end

endmodule