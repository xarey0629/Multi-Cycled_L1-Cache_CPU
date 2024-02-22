// Your code

//	Implemented instructions
//	auipc, jal, jalr
//	add, sub, and, xor
//	addi, slti, slli, srai
//	lw, sw
//	mul (No div)
//	beq

//	instruction	funct7	funct3	opcode
//	ADD         0000000 000     0110011
//	SUB         0100000 000		0110011
//	XOR			0000000	100		0110011			
// 	ADDI		imm		000		0010011
//	SLTI		imm		010		0010011
//	LW			imm		010		0000011
// 	SW          imm     010		0100011
// -------------------------------------
//	BEQ 		imm		000		1100011
//  BGE			imm		101		1100011
//  BLT			imm		100		1100011	
//  BNE			imm		001		1100011			
// -------------------------------------
//	JAL			imm		imm		1101111
//	JALR		imm		imm		1100111
//	AUIPC                       0010111
//	MUL
	


module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I
    );
    //==== I/O Declaration ========================
    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;

    //==== Reg/Wire Declaration ===================
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    wire   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
	wire [6:0] op;
	wire ALUSrc_A, ALUSrc_B, MemRead, MemWrite, Branch, jump, MulDiv ;
	wire [1:0] WDSrc, Aluop;
	wire [31:0] ALUin_A, ALUin_B, ALUout, ALUout_s, MDout;
	wire [31:0] PCaddr, PCinput, PCPlus4;
	wire [31:0] Immout, Writedata,InsData, mem_out;
	wire [31:0] Shiftout, Branchaddr;
	wire [3:0] alu_ctrl;
	wire Branch_enable, zero;
	wire mem_wen_D;
	wire valid;
	wire ready;
	wire [1:0] mode;
	assign mode = 0;
	
	assign InsData = mem_rdata_I;
	assign rs1 = InsData[19:15];
	assign rs2 = InsData[24:20];
	assign rd = InsData[11:7];
	//assign op = 7'd0;
	assign op = InsData[6:0];
	
    //==== Submodule Connection ===================
    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//

    // Todo: other submodules
	
	//mainController
	controller CTRL(
		.op(op), 
		.funct7(InsData[25]), 
		.funct3(InsData[14:12]), 
		.ALUSrc_A(ALUSrc_A), 
		.ALUSrc_B(ALUSrc_B), 
		.WDSrc(WDSrc), 
		.RegWrite(regWrite), 
		.MemRead(MemRead), 
		.MemWrite(MemWrite), 
		.Branch(Branch), 
		.jump(jump), 
		.MulDiv(MulDiv), 
		.Aluop(Aluop));
	
	
	
	//ALU CONTROL
	ALUcontrol ALUCtrl(
		.aluop(Aluop), 
		.funct7(InsData[30]), 
		.funct3(InsData[14:12]), 
		.alu_ctrl(alu_ctrl));
	//ALU
	ALU A1(
		.src_a(ALUin_A), 
		.src_b(ALUin_B),
		.funct3(InsData[14:12]),		
		.alu_ctrl(alu_ctrl), 
		.alu_out(ALUout), 
		.zero(zero) );
	
	//MUL/DIV //?
	
	mulDiv A2(
		.clk(clk), 
		.rst_n(rst_n), 
		.valid(valid), 
		.ready(ready), 
		.mode(mode), 
		.in_A(rs1_data), 
		.in_B(rs2_data), 
		.out(MDout));
	//valid <= (MulDiv==1)? 1:0;
	assign valid = (MulDiv==1)? 1:0;
	//immgeneration
	IMMGeneration IMMG(.in(InsData) ,.out(Immout));
    //==== Combinational Part =====================
	assign Branch_enable = Branch & zero;
	//InstructionMemory
	assign mem_addr_I = PC;//?
	//DataMemory //?
	DataMemory DM(
		.src(ALUout), 
		.rs_data(rs2_data), 
		.c1(MemRead), 
		.c2(MemWrite), 
		.addr(mem_addr_D), 
		.wen(mem_wen_D), 
		.mem_rdata_D(mem_rdata_D), 
		.mem_wdata_D(mem_wdata_D), 
		.out(mem_out));
	
	//assign mem_addr_D = ALUout;
    // Todo: any combinational/sequential circuit
	PCAdder adder0(.PC(PC), .PCPlus4(PCPlus4));
	Adder adder1(.src_a(PC), .src_b(Immout), .out(Branchaddr));
	//Shift shift1(.in(Immout), .out(Shiftout));
	MUX2way #(32)MUX1(.src_a(PCaddr), .src_b(ALUout),.c(jump),.out(PC_nxt));	//JumpMUX
	MUX2way #(32)MUX2(.src_a(PCPlus4), .src_b(Branchaddr),.c(Branch_enable),.out(PCaddr));	//BranchMUX
    MUX2way #(32)MUX3(.src_a(PC), .src_b(rs1_data),.c(ALUSrc_A),.out(ALUin_A));	//ALUSrc_AMUX
	MUX2way #(32)MUX4(.src_a(rs2_data), .src_b(Immout),.c(ALUSrc_B),.out(ALUin_B));	//ALUSrc_BMUX
	MUX2way #(32)MUX5(.src_a(ALUout), .src_b(MDout),.c(MulDiv),.out(ALUout_s));	//MUL/DIV
	MUX3way	#(32)MUX6(.src_a(ALUout_s), .src_b(mem_out), .src_c(PCPlus4), .c(WDSrc),.out(rd_data));//WDSrc
	//==== Sequential Part ========================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00400000; // Do not modify this value!!!
            
        end
        else begin
			
			if (MulDiv==1'b1)begin
				if (ready==1)
					PC <= PC_nxt;
			end
			else
				PC <= PC_nxt;
            
        end
    end
endmodule

//PCadder
module PCAdder(PC, PCPlus4);
	parameter BITS = 32;
	input [BITS-1:0] PC;
	output [BITS-1:0] PCPlus4;
	assign PCPlus4 = PC + 4; 
endmodule

//adder
module Adder(src_a, src_b, out);
	parameter BITS = 32;
	input [BITS-1:0] src_a, src_b;
	output [BITS-1:0] out;
	assign out = src_a + src_b; 
endmodule

//shift
module Shift(in, out);
	parameter BITS = 32;
	input [BITS-1:0] in;
	output [BITS-1:0] out;
	assign out = in << 1; 
endmodule

//MUX2way
module MUX2way #(parameter BITS = 32)(src_a, src_b, c, out);
	input [BITS-1:0] src_a, src_b;
	input c;
	output [BITS-1:0] out;
	assign out = (c == 1'b0) ? src_a:src_b;
endmodule

//MUX3way
module MUX3way #(parameter BITS = 32)(src_a, src_b, src_c, c, out);
	input [BITS-1:0] src_a, src_b, src_c;
	input [1:0] c;
	output [BITS-1:0] out;
	assign out = (c == 2'b10) ? src_c:(c == 2'b01) ? src_b:src_a;
endmodule

//IMMGen(not complete)
module IMMGeneration(in ,out);
	parameter BITS = 32;
	input [BITS-1:0] in;//ins[31:0]
	output reg [BITS-1:0] out;
	always @(*) begin
		case(in[6:0]) 
			7'b0010011 : out <= {{{BITS-12}{in[31]}}, in[31:20]}; 											//I-type -> addi, slti
			7'b0000011 : out <= {{{BITS-12}{in[31]}}, in[31:20]}; 											//lw-type
			7'b0100011 : out <= {{{BITS-12}{in[31]}}, {in[31:25], in[11:7]}};								//sw-type
			7'b1100011 : out <= {{{BITS-13}{in[31]}}, {in[31], in[7], in[30:25], in[11:8], {1{1'b0}}}};		//beq, bne, blt, bge
			7'b1101111 : out <= {{{BITS-21}{in[31]}}, {in[31], in[19:12], in[20], in[30:21], {1{1'b0}}}};	//jal
			//7'b1101111 : out <= {{{BITS-21}{in[31]}}, {in[31], in[21:12], in[22], in[30:23], 1'b0}};		//jal
			7'b1100111 : out <= {{{BITS-12}{in[31]}}, in[31:20]};											//jalr
			7'b0010111 : out <= {in[31:12], {{BITS-20}{1'b0}} };											//AUIPC
			default: out <= 32'bx;
		endcase
	end
endmodule

module ALU(src_a, src_b, funct3, alu_ctrl, alu_out, zero);
	parameter BITS = 32;
	input [BITS-1:0] src_a, src_b;
	wire [BITS-1:0] dis;
	input [3:0] alu_ctrl;
	input [2:0] funct3;
	output reg [BITS-1:0] alu_out;
	output reg zero; 
	// Update: 5/29 -> bne, blt
	wire beq, bne, blt, bge;
	assign beq = (alu_out == 0) ? 1 : 0;
	assign bne = (src_a != src_b) ? 1 : 0;
	assign dis = src_a - src_b;
	assign blt = (dis[31] == 1) ? 1 : 0;
	assign bge = (dis[31] == 0) ? 1 : 0;
	always @(*) 
	begin
		case(alu_ctrl)
			4'b0000: alu_out <= src_a & src_b;				//and
			4'b0001: alu_out <= src_a | src_b;				//or
			4'b0010: alu_out <= src_a + src_b;				//add
			4'b0110: alu_out <= src_a - src_b;				//sub
			4'b0111: alu_out <= src_a ^ src_b; 				//xor
			4'b0100: alu_out <= ((src_a) < (src_b)) ? 1:0; 	//slt
			4'b0011: alu_out <= src_a << src_b;				//sll
			4'b1010: alu_out <= src_a >>> src_b;			//sra
			default: alu_out <= 0;
		endcase
		case(funct3)
			// Update: 5/29 -> bne, blt
			3'b000: zero <= beq;
			3'b001: zero <= bne;
			3'b100: zero <= blt;
			3'b101: zero <= bge;
			default: zero <= 0;
		endcase
	end
endmodule
module ALUcontrol(aluop, funct7, funct3, alu_ctrl);
	input [1:0] aluop;
	input funct7; // funct7[5] or ins[30]
	input [2:0] funct3;
	output reg [3:0] alu_ctrl;
	always @(*)
	begin
		case(aluop)
			2'b00: alu_ctrl <= 4'b0010; //add(lw/sw/auipc/jal/jalr)
			2'b01: alu_ctrl <= 4'b0110;	
			//R-type
			2'b10: case({funct7, funct3})	
				4'b0000: alu_ctrl <= 4'b0010;	//add
				4'b1000: alu_ctrl <= 4'b0110;	//sub
				4'b0111: alu_ctrl <= 4'b0000;	//and
				4'b0110: alu_ctrl <= 4'b0001;	//or
				4'b0100: alu_ctrl <= 4'b0111;	//xor
				//default: alu_ctrl <= 4'bx;
			endcase
			2'b11:case({funct3})
				3'b000: alu_ctrl <= 4'b0010; // addi
				3'b010: alu_ctrl <= 4'b0100; // slti
				3'b001: alu_ctrl <= 4'b0011; // slli
				3'b101: alu_ctrl <= 4'b1010; // srai
				//default: alu_ctrl <= 4'bx;
			endcase
			default: alu_ctrl <= 4'bx; 
		endcase
	end
endmodule

// Controller(?not complete)
module controller(op, funct7, funct3, ALUSrc_A, ALUSrc_B, WDSrc, RegWrite, MemRead, MemWrite, Branch, jump, MulDiv, Aluop);
	input [6:0] op;
	input funct7; // funct7[0] or ins[25]
	input [2:0] funct3;
	output ALUSrc_A, ALUSrc_B, RegWrite, MemRead, MemWrite, Branch, jump, MulDiv;
	output [1:0] WDSrc, Aluop;
	reg [11:0] control;
	assign {ALUSrc_A, ALUSrc_B, WDSrc, RegWrite, MemRead, MemWrite, Branch, jump, MulDiv, Aluop} = control;
	always @(*) begin
		case(op)
			7'b0110011 : case({funct7})
				1'b1: control <= 12'b100010000110; // mul
				1'b0: control <= 12'b100010000010; // R-type -> add, sub, xor
				
				default: control <= 12'bx; 
			endcase
			7'b0010011 : control <= 12'b110010000011; // I-type -> addi, slti
			7'b0000011 : control <= 12'b110111000000; // lw-type -> lw //?
			7'b0100011 : control <= 12'b11xx00100000; // sw-type -> sw //?
			7'b1100011 : control <= 12'b10xx00010001; // B-type(SB) -> beq / bne / blt/ bge 
			7'b1100111 : control <= 12'b111010001000; // jalr-type
			7'b1101111 : control <= 12'b011010001000; // jal-type
			7'b0010111 : control <= 12'b010010000000; // auipc-type
			default : control <= 12'bx;
		endcase
	end
endmodule
module DataMemory (src, rs_data, c1, c2, addr, wen, mem_rdata_D, mem_wdata_D, out);
	parameter BITS = 32;
	//parameter addr_width = 5;
	input [BITS-1:0] src;
	input [BITS-1:0] rs_data;
	input c1, c2;
	input [BITS-1:0] mem_rdata_D;
	output reg wen;
	output reg [BITS-1:0] mem_wdata_D, out;
	output [BITS-1:0] addr; 
	
	assign addr = src;	//mem_addr_D = ALUout
	always @(*) begin
		if (c1 == 1'b1) begin
			wen <= 1'b0;	//mem_wen_D
			out <= mem_rdata_D;
		end
		else if (c2 == 1'b1) begin
			mem_wdata_D <= rs_data; //rd

			wen <= 1'b1;	//mem_wen_D
		end
		else
			wen <= 1'b0;
	end
endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0; // zero: hard-wired zero
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'h7fffeffc; // sp: stack pointer
                    32'd3: mem[i] <= 32'h10008000; // gp: global pointer
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end
    end
endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2 //?
	// Definition of ports
    input         clk, rst_n;
    input         valid;
    input  [1:0]  mode; // mode: 0: mulu, 1: divu, 2: shift, 3: avg
    output        ready;
    input  [31:0] in_A, in_B;
    //output [63:0] out;
	output [31:0] out;

    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter DIV  = 3'd2;
    parameter SHIFT = 3'd3;
    parameter AVG = 3'd4;
    parameter OUT  = 3'd5;

    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo: Instatiate any primitives if needed

    // Todo 5: Wire assignments
	assign ready = (state==OUT)? 1:0;
    //assign out = shreg;
	assign out = shreg[31:0];
	//assign out = shreg[63:32];
    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
				if (valid) begin
					if (mode==0) state_nxt <= MUL;
					else if (mode==1) state_nxt <= DIV;
					else if (mode==2) state_nxt <= SHIFT;
					else if (mode==3) state_nxt <= AVG;
				end else state_nxt <= IDLE;
            end
            MUL : begin
				if (counter==31) state_nxt <= OUT;
				else state_nxt <= MUL;
			end
            DIV : begin
				if (counter==31) state_nxt <= OUT;
				else state_nxt <= DIV;
			end
            SHIFT : state_nxt <= OUT;
            AVG : state_nxt <= OUT;
            OUT : state_nxt <= IDLE;
            default : state_nxt <= IDLE;
        endcase
    end
    // Todo 2: Counter
	always @(*) begin
		case(state)
			MUL: counter_nxt <= counter +1;
			DIV: counter_nxt <= counter +1;
			default : counter_nxt <= 0;
		endcase
    end
    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
	always @(*) begin
		case(state) 
			//IDLE: alu_out =0;
			MUL: begin
				if(shreg[0]==1) begin
					alu_out <= shreg[63:32] + alu_in_nxt;
				end else begin
					alu_out <= {1'b0, shreg[63:32]};
				end	
			end
			DIV: begin
				if (shreg[63:32] >= alu_in_nxt) begin
					alu_out <= shreg[63:32] - alu_in_nxt;
				end else begin
					alu_out <= {1'b0, shreg[63:32]};
				end
			end	
			SHIFT: begin
				alu_out <= shreg[31:0]>>alu_in_nxt[2:0];
			end	
			AVG: begin
				alu_out <= shreg[31:0] + alu_in_nxt;
			end
			default: alu_out <=0;
		endcase
	end
    
    // Todo 4: Shift register
	always @(*) begin
		case(state)
			MUL: shreg_nxt = {alu_out, shreg[31:0]} >> 1; //33+32-1(shift right)
			DIV: begin
				shreg_nxt = {alu_out[30:0], shreg[31:0], (shreg[63:32] >= alu_in_nxt)? 1'b1:1'b0}  ; // if (shreg[63:32] >= alu_in_nxt) =1 else =0
				if (counter==31) shreg_nxt = {1'b0, shreg_nxt[63:33], shreg_nxt[31:0]};
			end	
			SHIFT: shreg_nxt = {32'b0, alu_out};
			AVG: shreg_nxt = {32'b0, alu_out} >> 1;
			default: shreg_nxt = shreg;
		endcase
	end
    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
			counter <= 0; 
			shreg <= {32'b0,in_A};
        end
        else begin
            state <= state_nxt;
			counter <= counter_nxt;
			alu_in <= alu_in_nxt;
			shreg <= (state==IDLE) ?((mode==1)? {31'b0,in_A,1'b0}:{32'b0,in_A}): shreg_nxt;
        end
    end
endmodule