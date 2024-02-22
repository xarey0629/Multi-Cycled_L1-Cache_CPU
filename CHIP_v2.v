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

//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//
module CHIP #(                                                                                  //
    parameter BIT_W = 32                                                                        //
)(                                                                                              //
    // clock                                                                                    //
        input               i_clk,                                                              //
        input               i_rst_n,                                                            //
    // instruction memory                                                                       //
        input  [BIT_W-1:0]  i_IMEM_data,                                                        //
        output [BIT_W-1:0]  o_IMEM_addr,                                                        //
        output              o_IMEM_cen, //addition                                                          //
    // data memory                                                                              //
        input               i_DMEM_stall, //addition                                                        //
        input  [BIT_W-1:0]  i_DMEM_rdata,                                                       //
        output              o_DMEM_cen, //addition                                                         //
        output              o_DMEM_wen,                                                         //
        output [BIT_W-1:0]  o_DMEM_addr,                                                        //
        output [BIT_W-1:0]  o_DMEM_wdata                                                        //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any declaration

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg [BIT_W-1:0] PC, next_PC;
        wire mem_cen, mem_wen;
        wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata; //?
        wire mem_stall;
		
		wire [6:0] op;
		wire ALUSrc_A, ALUSrc_B, regWrite, MemRead, MemWrite, Branch, jump, MulDiv ;
		wire [1:0] WDSrc, Aluop;
		wire [31:0] ALUin_A, ALUin_B, ALUout, ALUout_s, MDout;
		wire [31:0] PCaddr, PCinput, PCPlus4;
		wire [31:0] Immout, InsData, mem_out;
		wire [31:0] Shiftout, Branchaddr;
		wire [3:0] alu_ctrl;
		wire Branch_enable, zero;
		wire o_DMEM_wen;
		wire i_valid;
		wire ready;
		wire [1:0] mode;
		assign mode = 0;
		
		
		//register
		wire   [ 4:0] rs1, rs2, rd;              //
		wire   [31:0] rs1_data    ;              //
		wire   [31:0] rs2_data    ;              //
		wire   [31:0] rd_data     ;              //
		//assign InsData = i_IMEM_data;
		assign rs1 = InsData[19:15];
		assign rs2 = InsData[24:20];
		assign rd = InsData[11:7];
		assign op = InsData[6:0];
		
		
// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------
	
    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (regWrite),          
        .rs1    (rs1),                
        .rs2    (rs2),                
        .rd     (rd),                 
        .wdata  (rd_data),             
        .rdata1 (rs1_data),           
        .rdata2 (rs2_data)
    );
	
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
		
	//MUL/DIV
	MULDIV_unit A2(
		.i_clk(i_clk), 
		.i_rst_n(i_rst_n), 
		.i_valid(i_valid), 
		.o_done(ready), 
		.mode(mode), 
		.i_A(rs1_data), 
		.i_B(rs2_data), 
		.o_data(MDout));
	assign valid = (MulDiv==1)? 1:0;
	
	//immgeneration
	IMMGeneration IMMG(
	.in(InsData) ,
	.out(Immout));
	
	//Branch_enable
	assign Branch_enable = Branch & zero;
	
	//InstructionMemory //?
	//assign o_IMEM_addr = PC;
	InstMemory IM (.pc_addr(PC), 
	.o_IMEM_addr(o_IMEM_addr),
	.i_IMEM_data(i_IMEM_data), 
	.InsData(InsData) );
	//DataMemory // ?
	DataMemory DM(
		.src(ALUout), 
		.rs_data(rs2_data), 
		.c1(MemRead), 
		.c2(MemWrite), 
		.addr(mem_addr_D), 
		.wen(o_DMEM_wen), 
		.mem_rdata_D(i_DMEM_rdata), 
		.mem_wdata_D(o_DMEM_wdata), 
		.out(mem_out));
		
	//Adder
	PCAdder adder0(.PC(PC), .PCPlus4(PCPlus4));
	Adder adder1(.src_a(PC), .src_b(Immout), .out(Branchaddr));
	//MUX
	MUX2way #(32)MUX1(.src_a(PCaddr), .src_b(ALUout),.c(jump),.out(PC_nxt));	//JumpMUX
	MUX2way #(32)MUX2(.src_a(PCPlus4), .src_b(Branchaddr),.c(Branch_enable),.out(PCaddr));	//BranchMUX
    MUX2way #(32)MUX3(.src_a(PC), .src_b(rs1_data),.c(ALUSrc_A),.out(ALUin_A));	//ALUSrc_AMUX
	MUX2way #(32)MUX4(.src_a(rs2_data), .src_b(Immout),.c(ALUSrc_B),.out(ALUin_B));	//ALUSrc_BMUX
	MUX2way #(32)MUX5(.src_a(ALUout), .src_b(MDout),.c(MulDiv),.out(ALUout_s));	//MUL/DIV
	MUX3way	#(32)MUX6(.src_a(ALUout_s), .src_b(mem_out), .src_c(PCPlus4), .c(WDSrc),.out(rd_data));//WDSrc
// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
			//o_IMEM_cen <= 0;
			
        end
        else begin
            if (MulDiv==1'b1)begin
				if (ready==1)
					PC <= PC_nxt;
					//o_IMEM_cen <= 1;
			end
			else
				PC <= PC_nxt;
				//o_IMEM_cen <= 1;
            
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
			4'b0011: alu_out <= src_a << src_b;				//sll (<< no extension)
			4'b1010: alu_out <= src_a >>> src_b;			//sra (>>> singed extension) 
			default: alu_out <= 0;
		endcase
		case(funct3)
			// Update: 5/29 -> bne, blt
			3'b000: zero <= beq;
			3'b001: zero <= bne;
			3'b100: zero <= blt;
			3'b101: zero <= bge;
			default: zero<= 0;
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

//controller(?not complete)
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
				1'b1: control <= 12'b100010000110; //mul
				1'b0: control <= 12'b100010000010; //R-type -> add, sub, xor
				
				default: control <= 12'bx; 
			endcase
			7'b0010011 : control <= 12'b110010000011; // I-type -> addi, slti
			7'b0000011 : control <= 12'b110111000000; // lw-type -> lw //?
			7'b0100011 : control <= 12'b11xx00100000; // sw-type -> sw //?
			7'b1100011 : control <= 12'b10xx00010001; // beq, bne, blt, bge
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
			//if stall==0
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

module InstMemory (pc_addr, o_IMEM_addr, i_IMEM_data, InsData );
	parameter BITS = 32;
	
	input [BITS-1:0] pc_addr;
	input [BITS-1:0] i_IMEM_data;
	
	output [BITS-1:0] o_IMEM_addr
	output [BITS-1:0] InsData;
	
	assign o_IMEM_addr = PC;
	assign InsData = i_IMEM_data;
	
endmodule

module Reg_file(i_clk, i_rst_n, wen, rs1, rs2, rd, wdata, rdata1, rdata2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input i_clk, i_rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] wdata;
    input [addr_width-1:0] rs1, rs2, rd;

    output [BITS-1:0] rdata1, rdata2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign rdata1 = mem[rs1];
    assign rdata2 = mem[rs2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (rd == i)) ? wdata : mem[i];
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
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

module MULDIV_unit(
	// Definition of ports
    input         i_clk, i_rst_n,
    input         i_valid,
    input  [1:0]  mode, // mode: 0: mulu, 1: divu
    output        o_done,
    input  [31:0] i_A, i_B,
    //output [63:0] out;
	output [31:0] o_data
    );
    // Todo: HW2
	
	// Parameters
    // Definition of states
    parameter S_IDLE = 3'd0;
    parameter S_MUL = 3'd1;
    parameter S_DIV = 3'd2;
    parameter S_OUT = 3'd3;
	
	// Wires & Regs
    reg  [3:0] state, next_state;
	reg  [ 4:0] counter, next_counter;
	reg  [63:0] shreg, next_shreg;
	reg  [31:0] alu_in, next_alu_in;
	reg  [32:0] alu_out;
	reg overflow;
	
	// Wire Assignments
	assign o_done = (state==S_OUT)? 1:0;
    assign o_data = shreg;
	
	// Always Combination
	always @(*) begin
        case(state)
            S_IDLE: begin
				if (i_valid) begin
					if (mode==0) next_state <= S_MUL;
					else if (mode==1) next_state <= S_DIV;
				end else next_state <= S_IDLE;
            end
            S_MUL : begin
				if (counter==31) next_state <= S_OUT;
				else next_state <= S_MUL;
			end
            S_DIV : begin
				if (counter==31) next_state <= S_OUT;
				else next_state <= S_DIV;
			end
            S_OUT : next_state <= S_IDLE;
            default : next_state <= S_IDLE;
        endcase
	end
	//Counter
	always @(*) begin
		case(state)
			S_MUL: next_counter <= counter +1;
			S_DIV: next_counter <= counter +1;
			default : next_counter <= 0;
		endcase
    end
	
	// ALU input
    always @(*) begin
        case(state)
            S_IDLE: begin
                if (i_valid) next_alu_in = i_B;
                else         next_alu_in = 0;
            end
            S_OUT : next_alu_in = 0;
            default: next_alu_in = alu_in;
        endcase
    end
	
	//ALU output
    always @(*) begin
		case(state)
			S_MUL: begin
				if (shreg[0]==1) alu_out <= shreg[63:32] + next_alu_in;
				else alu_out <= {1'b0, shreg[63:32]};
			end
			S_DIV: begin
				if (shreg[63:32] >= next_alu_in) alu_out <= shreg[63:32] - next_alu_in;
				else alu_out <= {1'b0, shreg[63:32]};
			end
			default: alu_out <=0;
		endcase
	end
	
	//Shift register
	always @(*) begin
		case(state)
			S_MUL: next_shreg = {alu_out, shreg[31:0]} >>1; //33+32-1 (shift right)
			S_DIV: begin				
				next_shreg = {alu_out[30:0], shreg[31:0], (shreg[63:32] >= next_alu_in)? 1'b1:1'b0};
				if (counter==31) next_shreg = {alu_out[31], next_shreg[63:33], next_shreg[31:0]};
			end
			default: next_shreg = shreg;
		endcase
	end
	
	//Sequential always block
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state <= S_IDLE;
			counter <= 0; 
			shreg <= {32'b0, i_A};
        end
        else begin
            state <= next_state;
			counter <= next_counter;
			alu_in <= next_alu_in;
			shreg <= (state==S_IDLE) ?((mode==1)? {31'b0,i_A,1'b0}:{32'b0,i_A}) : next_shreg;
        end
    end
	
endmodule

module Cache#(
        parameter BIT_W = 32,
        parameter ADDR_W = 32
    )(
        input i_clk,
        input i_rst_n,
        // processor interface
            input i_proc_cen,
            input i_proc_wen,
            input [ADDR_W-1:0] i_proc_addr,
            input [BIT_W-1:0]  i_proc_wdata,
            output [BIT_W-1:0] o_proc_rdata,
            output o_proc_stall,
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W-1:0]  o_mem_wdata,
            input [BIT_W-1:0] i_mem_rdata,
            input i_mem_stall
    );

    //---------------------------------------//
    //          default connection           //
    assign o_mem_cen = i_proc_cen;        //
    assign o_mem_wen = i_proc_wen;        //
    assign o_mem_addr = i_proc_addr;      //
    assign o_mem_wdata = i_proc_wdata;    //
    assign o_proc_rdata = i_mem_rdata;    //
    assign o_proc_stall = i_mem_stall;    //
    //---------------------------------------//

    // Todo: BONUS
endmodule