`include "reg32.v"
`include "mux2.v"
`include "mux3.v"
`include "control_pipeline.v"
`include "alu.v"
`include "alu_ctl.v"
`include "add32.v"
`include "rom32.v"
`include "mem32.v"
`include "reg_file.v"

module mips_pipeline(clk, reset);
    input clk, reset;

    reg  [31:0] IF_pc;
    wire [31:0] IF_instr, IF_pc_maybestalled, IF_pc_jump, IF_pc_next, IF_pc4;
    reg         Stall;
    reg  [31:0] ID_instr, ID_pc4;
    wire [5:0]  ID_op, ID_funct;
    wire [4:0]  ID_rs, ID_rt, ID_rd;
    wire [15:0] ID_immed;
    wire [31:0] ID_extend, ID_rd1, ID_rd2;
    wire [31:0] ID_jaddr;
    wire        ID_RegWrite_v, ID_MemWrite_v, ID_MemRead_v, ID_Branch_v, ID_Jump_v;
    wire        ID_RegWrite, ID_Branch, ID_RegDst, ID_MemtoReg, ID_MemRead;
    wire        ID_MemWrite, ID_ALUSrc, ID_Jump;
    wire [1:0]  ID_ALUOp;
    reg  [31:0] EX_pc4, EX_extend, EX_rd1, EX_rd2;
    wire [31:0] EX_offset, EX_btgt, EX_alub, EX_ALUOut;
    reg  [4:0]  EX_rs, EX_rt, EX_rd;
    wire [4:0]  EX_RegRd;
    wire [5:0]  EX_funct;
    reg         EX_RegWrite, EX_Branch, EX_RegDst, EX_MemtoReg, EX_MemRead, EX_MemWrite, EX_ALUSrc;
    wire        EX_Zero;
    reg  [1:0]  EX_ALUOp;
    wire [2:0]  EX_Operation;
    reg  [1:0]  ForwardA, ForwardB;
    wire        MEM_PCSrc;
    reg         MEM_RegWrite, MEM_Branch, MEM_MemtoReg, MEM_MemRead, MEM_MemWrite, MEM_Zero;
    reg  [31:0] MEM_btgt, MEM_ALUOut, MEM_rd2;
    wire [31:0] MEM_memout;
    reg  [5:0]  MEM_RegRd;
    reg         WB_RegWrite, WB_MemtoReg;
    reg  [31:0] WB_memout, WB_ALUOut;
    wire [31:0] WB_wd;
    reg  [4:0]  WB_RegRd;
    reg  [31:0] IF_PC_d_out;
    wire [31:0] MuxA_out, MuxB_out;
    reg  [31:0] WB_wd_reg;

    // ********************************************************************
    //                              IF Stage
    // ********************************************************************

    always @(posedge clk)
        if (reset)
            IF_pc <= 0;
        else
            IF_pc <= IF_pc_next;

    add32      IF_PCADD(IF_pc, 32'd4, IF_pc4);
    mux2 #(32) IF_SMUX(Stall, IF_pc4, IF_pc, IF_pc_maybestalled);
    mux2 #(32) IF_JMPMUX(ID_Jump, IF_pc_maybestalled, ID_jaddr, IF_pc_jump);
    mux2 #(32) IF_PCMUX(MEM_PCSrc, IF_pc_jump, MEM_btgt, IF_pc_next);
    rom32      IMEM(IF_pc, IF_instr);

    always @(posedge clk) begin
        if (reset) begin
            ID_instr <= 0;
            ID_pc4   <= 0;
        end else begin
            if (ID_Jump)
                ID_instr <= 0;
            else if (Stall)
                ID_instr <= ID_instr;
            else
                ID_instr <= IF_instr;
            ID_pc4   <= IF_pc4;
        end
    end

    // ********************************************************************
    //                              ID Stage
    // ********************************************************************

    assign ID_op    = ID_instr[31:26];
    assign ID_rs    = ID_instr[25:21];
    assign ID_rt    = ID_instr[20:16];
    assign ID_rd    = ID_instr[15:11];
    assign ID_immed = ID_instr[15:0];

    reg_file RFILE(clk, WB_RegWrite, ID_rs, ID_rt, WB_RegRd, ID_rd1, ID_rd2, WB_wd);

    assign ID_extend = { {16{ID_immed[15]}}, ID_immed };
    assign ID_jaddr = {ID_pc4[31:28], ID_instr[25:0], 2'b00};

    always @(*) begin
        if (EX_MemRead && ((EX_rt == ID_rs) || (EX_rt == ID_rt)))
            Stall = 1'b1;
        else
            Stall = 1'b0;
    end

    control_pipeline CTL(.opcode(ID_op),           .RegDst(ID_RegDst),
                         .ALUSrc(ID_ALUSrc),       .MemtoReg(ID_MemtoReg),
                         .RegWrite(ID_RegWrite_v), .MemRead(ID_MemRead_v),
                         .MemWrite(ID_MemWrite_v), .Branch(ID_Branch_v),
                         .ALUOp(ID_ALUOp),         .Jump(ID_Jump_v));

    mux2 #(1) ID_RW_SMUX(Stall, ID_RegWrite_v, 1'b0, ID_RegWrite);
    mux2 #(1) ID_MR_SMUX(Stall, ID_MemRead_v,  1'b0, ID_MemRead);
    mux2 #(1) ID_MW_SMUX(Stall, ID_MemWrite_v, 1'b0, ID_MemWrite);
    mux2 #(1) ID_BR_SMUX(Stall, ID_Branch_v,   1'b0, ID_Branch);
    mux2 #(1) ID_JU_SMUX(Stall, ID_Jump_v,     1'b0, ID_Jump);

    always @(posedge clk) begin
        if (reset) begin
            EX_ALUOp    <= 0;
            EX_ALUSrc   <= 0;
            EX_Branch   <= 0;
            EX_MemRead  <= 0;
            EX_MemWrite <= 0;
            EX_MemtoReg <= 0;
            EX_RegDst   <= 0;
            EX_RegWrite <= 0;
            EX_extend   <= 0;
            EX_pc4      <= 0;
            EX_rd       <= 0;
            EX_rd1      <= 0;
            EX_rd2      <= 0;
            EX_rs       <= 0;
            EX_rt       <= 0;
        end else begin
            EX_ALUOp    <= ID_ALUOp;
            EX_ALUSrc   <= ID_ALUSrc;
            EX_Branch   <= ID_Branch;
            EX_MemRead  <= ID_MemRead;
            EX_MemWrite <= ID_MemWrite;
            EX_MemtoReg <= ID_MemtoReg;
            EX_RegDst   <= ID_RegDst;
            EX_RegWrite <= ID_RegWrite;
            EX_extend   <= ID_extend;
            EX_pc4      <= ID_pc4;
            EX_rd       <= ID_rd;
            EX_rd1      <= ID_rd1;
            EX_rd2      <= ID_rd2;
            EX_rs       <= ID_rs;
            EX_rt       <= ID_rt;
        end
    end

    // ********************************************************************
    //                              EX Stage
    // ********************************************************************

    assign EX_offset = EX_extend << 2;
    assign EX_funct = EX_extend[5:0];

    add32 EX_BRADD(EX_pc4, EX_offset, EX_btgt);

    mux3 #(32)  FMUXA(ForwardA, EX_rd1, WB_wd, MEM_ALUOut, MuxA_out);
    mux3 #(32)  FMUXB(ForwardB, EX_rd2, WB_wd, MEM_ALUOut, MuxB_out);
    mux2 #(32) 	ALUMUX(EX_ALUSrc, MuxB_out, EX_extend, EX_alub);
    alu         EX_ALU(EX_Operation, MuxA_out, EX_alub, EX_ALUOut, EX_Zero);
    mux2 #(5)   EX_RFMUX(EX_RegDst, EX_rt, EX_rd, EX_RegRd);
    alu_ctl     EX_ALUCTL(EX_ALUOp, EX_funct, EX_Operation);


    always @(*) begin
        if (MEM_RegWrite && (MEM_RegRd != 0) && (MEM_RegRd == EX_rs))
            ForwardA = 2'b10;
        else if (WB_RegWrite && (WB_RegRd != 0) && !(MEM_RegWrite && (MEM_RegRd != 0) && (MEM_RegRd != EX_rs)) && (WB_RegRd == EX_rs))
            ForwardA = 2'b01;
        else
            ForwardA = 2'b00;

        if (MEM_RegWrite && (MEM_RegRd != 0) && (MEM_RegRd == EX_rt))
            ForwardB = 2'b10;
        else if (WB_RegWrite && (WB_RegRd != 0) && !(MEM_RegWrite && (MEM_RegRd != 0) && (MEM_RegRd != EX_rt)) && (WB_RegRd == EX_rt))
            ForwardB = 2'b01;
        else
            ForwardB = 2'b00;
    end


    always @(posedge clk) begin
        if (reset) begin
            MEM_ALUOut   <= 0;
            MEM_Branch   <= 0;
            MEM_MemRead  <= 0;
            MEM_MemWrite <= 0;
            MEM_MemtoReg <= 0;
            MEM_RegRd    <= 0;
            MEM_RegWrite <= 0;
            MEM_Zero     <= 0;
            MEM_btgt     <= 0;
            MEM_rd2      <= 0;
        end else begin
            MEM_ALUOut   <= EX_ALUOut;
            MEM_Branch   <= EX_Branch;
            MEM_MemRead  <= EX_MemRead;
            MEM_MemWrite <= EX_MemWrite;
            MEM_MemtoReg <= EX_MemtoReg;
            MEM_RegRd    <= EX_RegRd;
            MEM_RegWrite <= EX_RegWrite;
            MEM_Zero     <= EX_Zero;
            MEM_btgt     <= EX_btgt;
            MEM_rd2      <= EX_rd2;
        end
    end

    // ********************************************************************
    //                              MEM Stage
    // ********************************************************************

    mem32 MEM_DMEM(clk, MEM_MemRead, MEM_MemWrite, MEM_ALUOut, MEM_rd2, MEM_memout);
    and   MEM_BR_AND(MEM_PCSrc, MEM_Branch, MEM_Zero);

    always @(posedge clk) begin
        if (reset) begin
            WB_ALUOut   <= 0;
            WB_MemtoReg <= 0;
            WB_RegRd    <= 0;
            WB_RegWrite <= 0;
            WB_memout   <= 0;
        end else begin
            WB_ALUOut   <= MEM_ALUOut;
            WB_MemtoReg <= MEM_MemtoReg;
            WB_RegRd    <= MEM_RegRd;
            WB_RegWrite <= MEM_RegWrite;
            WB_memout   <= MEM_memout;
        end
    end

    // ********************************************************************
    //                              WB Stage
    // ********************************************************************

    mux2 #(32) WB_WRMUX(WB_MemtoReg, WB_ALUOut, WB_memout, WB_wd);

    always @(posedge clk)
        WB_wd_reg <= WB_wd;

endmodule