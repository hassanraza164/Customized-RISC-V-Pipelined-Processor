`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    12:49:01 01/10/2021 
// Design Name: 
// Module Name:    Basic RISC-V single cycle implementation on Verilog 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
module main(rst,interrupt, clk, alu_z, Anode_Activate, LED_out);
input rst, clk, interrupt;						// 1 button to reset, clock signal as input
output alu_z;						// An LED turned ON if result is zero
output reg[7:0] Anode_Activate;		// Anodes to control 7-segments
output reg [6:0] LED_out;			// output result to be sent on 7-segments



	// ALL modules will be called in this file. Code will be executed and results will be shown on 7-segment display
// Code segment for BCD to 7-segment Decoder. Keep this code as it is
reg [31:0] counter ;		// A 32 bit flashing counter
reg toggle;			// A variable to toggle between two 7-segments 

always @(posedge clk)
    begin
            if (!rst)begin
            if(counter>=100000) begin //100000
                 counter <= 0;
				 toggle = ~toggle; end
            else begin
                counter <= counter + 1;
				end
			end
			else begin
			     toggle<=0;
			     counter<=0;
			     end
    end 
    // anode activating signals for 8 segments, digit period of 1ms
    // decoder to generate anode signals 
    always @(*)
    begin
        case(toggle)
        1'b0: begin
            Anode_Activate = 8'b01111111; 
            // activate SEGMENT1 and Deactivate all others
              end
        1'b1: begin
            Anode_Activate = 8'b10111111; 
            // activate LED2 and Deactivate all others    
               end
        endcase
    end
    // Cathode patterns of the 7-segment 1 LED display 
wire [31:0] result;

    always @(*)
    begin
	if (toggle) begin
        case(result)				// First 4 bits of Result from ALU will be displayed on 1st segment
        32'b0000: LED_out = 7'b0000001; // "0"     
        32'b0001: LED_out = 7'b1001111; // "1" 
        32'b0010: LED_out = 7'b0010010; // "2" 
        32'b0011: LED_out = 7'b0000110; // "3" 
        32'b0100: LED_out = 7'b1001100; // "4" 
        32'b0101: LED_out = 7'b0100100; // "5" 
        32'b0110: LED_out = 7'b0100000; // "6" 
        32'b0111: LED_out = 7'b0001111; // "7" 
        32'b1000: LED_out = 7'b0000000; // "8"     
        32'b1001: LED_out = 7'b0000100; // "9"
		32'b1010: LED_out = 7'b0001000; // "A"     
        32'b1011: LED_out = 7'b1100000; // "b"     
        32'b1100: LED_out = 7'b0110001; // "C"     
        32'b1101: LED_out = 7'b1000010; // "d"     
        32'b1110: LED_out = 7'b0110000; // "E"     
        32'b1111: LED_out = 7'b0111000; // "F"     
        
        default: LED_out = 7'b0000001; // "0"
        endcase
		end
    

	// Cathode patterns of the 7-segment 2 LED display
        if(!toggle) begin	
        case(result[7:4])			// Next 4 bits of Result from ALU will be displayed on 2nd segment
        4'b0000: LED_out = 7'b0000001; // "0"     
        4'b0001: LED_out = 7'b1001111; // "1" 
        4'b0010: LED_out = 7'b0010010; // "2" 
        4'b0011: LED_out = 7'b0000110; // "3" 
        4'b0100: LED_out = 7'b1001100; // "4" 
        4'b0101: LED_out = 7'b0100100; // "5" 
        4'b0110: LED_out = 7'b0100000; // "6" 
        4'b0111: LED_out = 7'b0001111; // "7" 
        4'b1000: LED_out = 7'b0000000; // "8"     
        4'b1001: LED_out = 7'b0000100; // "9"
		4'b1010: LED_out = 7'b0001000; // "A"     
        4'b1011: LED_out = 7'b1100000; // "b"     
        4'b1100: LED_out = 7'b0110001; // "C"     
        4'b1101: LED_out = 7'b1000010; // "d"     
        4'b1110: LED_out = 7'b0110000; // "E"     
        4'b1111: LED_out = 7'b0111000; // "F"     
        
        default: LED_out = 7'b0000001; // "0"
        endcase
    end
end

	// Keep writing your code (calling lower module) here!
	
	
	wire [31:0] pc_next,pc_next1,PCPlus4F, instruction, RD1, RD2, PCF;
    reg [31:0] pc;
    wire  ALU_SrcD, carry, MemWriteD, RegwriteD, ret,FlushM;
    wire [1:0] Imm_SrcD, Result_SrcD;
    wire [31:0] ImmExtD;
    wire [3:0] ALUControlD;
    wire En1, En2, CLR, CLR1;
	
	//initial  // initial pc
    //pc = 32'h0; 
    
    always @ (posedge clk) begin // address Generator
        if(rst)
        pc = 32'h0;
       // else begin
        else if (En1)
        pc = pc;
        else
        pc = pc_next1; 
        //end    
    end
    
    
    assign PCF = pc; 
    Instruction_Memory IM(.pc(pc),.instruction(instruction)); // fetching the instruction
    
    // Calling the Control Unit
    
    // 1st phase
    reg [95:0] reg_1;
  
    always @ (posedge clk)  begin
    if (!rst && !En2 && !CLR1) begin
    
        reg_1 [31:0] = PCPlus4F;
        
        reg_1 [63:32] = PCF;
        
        reg_1 [95:64] = instruction;
    
    end
    else if (CLR1 || rst)
    reg_1 = 96'd0;
    
    end
    
    wire [31:0]  instrD, PCD, PCPlus4D;
    
    
    assign instrD = reg_1 [95:64];
    
    assign PCD =  reg_1 [63:32];
    
    assign PCPlus4D = reg_1 [31:0];
   
   
 // D phase 
 wire jumpD, branchD;
 
 wire [4:0] RdD, Rs1D, Rs2D;
 
 assign RdD = instrD[11:7];
 
 assign Rs1D = instrD[19:15];
 
 assign Rs2D = instrD[24:20];
 
 reg [185:0] reg_2;
 
 
     always @ (posedge clk)  begin
     
     if (!CLR) begin
         reg_2 [31:0] = PCPlus4D;
         
         reg_2 [63:32] = ImmExtD;
         
         reg_2 [68:64] = RdD;
         
         reg_2 [100:69] =PCD;
         
         reg_2 [132:101] = RD2;
         
         reg_2 [164:133] = RD1;
         
         reg_2 [165] = ALU_SrcD;
         
         reg_2 [169:166] = ALUControlD;
         
         reg_2 [170] = branchD;
         
         reg_2 [171] = jumpD;
         
         reg_2 [172] = MemWriteD;
         
         reg_2 [174:173] = Result_SrcD;
         
         reg_2 [175] = RegwriteD;
         
         reg_2 [180:176] = Rs1D;
         
         reg_2 [185:181] = Rs2D;
         
         end
         
         else
         reg_2 = 186'd0;
     
     end
     
     
     wire  ALU_SrcE, MemWriteE, RegwriteE, PC_SrcE, zeroE, jumpE, branchE, temp;
         wire [1:0]  Result_SrcE;
         wire [31:0] ImmExtE, PCPlus4E, PCE, RD1E, RD2E, ALUResultE,pc_targetE, SrcBE, Operand2E,WriteDataE;
         wire [3:0] ALUControlE;
         wire [4:0] RdE,Rs1E,Rs2E;
         
      assign WriteDataE = Operand2E;
         
      assign RegwriteE = reg_2 [175]; 
     
      assign Result_SrcE = reg_2 [174:173];
      
      assign MemWriteE=  reg_2 [172];
      
      assign jumpE = reg_2 [171]; 
      
      assign branchE = reg_2 [170]; 
     
      and (temp, branchE, zeroE);
     
      or (PC_SrcE, jumpE, temp);
      
      assign ALUControlE =  reg_2 [169:166]; 
     
      assign ALU_SrcE = reg_2 [165];   
         
      assign RD1E = reg_2 [164:133]; 
      
      assign RD2E = reg_2 [132:101];
      
      assign PCE = reg_2 [100:69];
      
      assign RdE =  reg_2 [68:64];  
      
      assign ImmExtE = reg_2 [63:32];
      
      assign PCPlus4E =  reg_2 [31:0];
      
      assign Rs1E = reg_2 [180:176];
      
      assign Rs2E = reg_2 [185:181];
      
      // phase E
      
      
       reg [104:0] reg_3;
       
       always @ (posedge clk ) begin
       if (!FlushM)begin
       reg_3 [31:0] = PCPlus4E;
       
       reg_3 [36:32] = RdE;
       
       reg_3 [68:37] = WriteDataE;
       
       reg_3 [100:69] = ALUResultE;
       
       reg_3 [101] =  MemWriteE;  
       
       reg_3 [103:102] = Result_SrcE;
       
       reg_3 [104] =  RegwriteE ;
       end
       else
       reg_3 = 105'd0;
       end
       
       
      
                wire  MemWriteM, RegwriteM;
                wire [1:0] Result_SrcM;
                wire [31:0]  PCPlus4M, WriteDataM, ALUResultM, ReadDataM;
                wire [4:0] RdM;
                
       assign RegwriteM = reg_3 [104];
       
       assign Result_SrcM = reg_3 [103:102];
       
       assign MemWriteM = reg_3 [101];
       
       assign ALUResultM = reg_3 [100:69];
       
       assign WriteDataM = reg_3 [68:37]; // RD2
       
       assign RdM = reg_3 [36:32];
       
       assign PCPlus4M = reg_3 [31:0];
      
      
      // phase endd
      
      
      reg [103:0] reg_4;
      
      
      always @ (posedge clk) begin
        
        reg_4 [31:0] = PCPlus4M;
        
        reg_4 [36:32] = RdM;
        
        reg_4 [68:37] = ReadDataM;
        
        reg_4 [100:69] = ALUResultM;
        
        reg_4 [102:101] = Result_SrcM;
        
        reg_4 [103] = RegwriteM;
      
      end
      
      
      wire  RegwriteW;
      wire [1:0] Result_SrcW;
      wire [31:0]  PCPlus4W, ALUResultW, ReadDataW, ResultW;
      wire [4:0] RdW;
      
      assign  RegwriteW = reg_4 [103];
      
      assign  Result_SrcW = reg_4 [102:101];
     
      assign  ALUResultW = reg_4 [100:69];
      
      assign  ReadDataW = reg_4 [68:37];
    
      assign  RdW  = reg_4 [36:32];
     
      assign  PCPlus4W = reg_4 [31:0];
      
      
      
      // Hazard Unit
      wire [1:0]  ForwardAE, ForwardBE;
      
      wire [31:0] SrcAE;
     
      wire PC_CSR,interrupt_pending; 
      
      HazardUnit HU(.Rs1E(Rs1E),.Rs2E(Rs2E),.ForwardAE(ForwardAE),.ForwardBE(ForwardBE),.RdM(RdM),.RdW(RdW),.RegWriteM(RegwriteM),.RegWriteW(RegwriteW),
      .ResultSrc0(Result_SrcE[0]),.RdE(RdE),.Rs1D(Rs1D),.Rs2D(Rs2D),.StallF(En1),.StallD(En2),.FlushE(CLR),.PCSrcE(PC_SrcE),.FlushD(CLR1),.intrupt(interrupt_pending),.FlushM(FlushM),.ret(ret));
      
      mux3x1 operandA(.a(RD1E),.b(ResultW),.c(ALUResultM),.sel(ForwardAE),.o(SrcAE));
      
      mux3x1 operandB(.a(RD2E),.b(ResultW),.c(ALUResultM),.sel(ForwardBE),.o(Operand2E));
      
      
     
    Control_Unit CU( .op(instrD[6:0]),.funct3(instrD[14:12]),.funct7(instrD[30]),.Result_Src(Result_SrcD),.MemWrite(MemWriteD),.ALU_Src(ALU_SrcD),.RegWrite(RegwriteD),.ALUControl(ALUControlD),.Imm_Src(Imm_SrcD),.jump(jumpD), 
    .branch(branchD),.ret(ret));        
     
     //Register File calling       
            
    register_file R_F(.Port_A(RD1),.Port_B(RD2),.Din(ResultW), .Addr_A(instrD[19:15]), .Addr_B(instrD[24:20]), .Addr_Wr(RdW),.wr(RegwriteW),.Hard_wired(result), .clk(clk)); // complete
            
         // immediate Extender
         
    extend Ext(.instr(instrD[31:7]),.immsrc(Imm_SrcD),.immext(ImmExtD)); // complete
    
    // Mux 2 into 1 for 2nd operand Selector
            
    mux2x1 mux1(.a(ImmExtE),.b(Operand2E),.sel(ALU_SrcE),.o(SrcBE)); // complete ScrB
    
    //ALU calling
          
    alu ALU(.A(SrcAE),.B(SrcBE),.ALU_Sel(ALUControlE),.ALU_Out(ALUResultE),.CarryOut(carry),.ZeroOut(zeroE));
    
    //Data Memory
  
            
    Data_Memory D_M(.Data_Out(ReadDataM),.Data_In(WriteDataM),.D_Addr(ALUResultM),.wr(MemWriteM),.clk(clk) );
    
    //Two Pc's Adders
    
    adder add1(.a(pc),.b(32'd4),.y(PCPlus4F));
    adder add2(.a(PCE),.b(ImmExtE),.y(pc_targetE)); 
    
    
    // MUX 3*1 for PC_Result
            
    mux3x1 result_mux(.a(ALUResultW),.b(ReadDataW),.c(PCPlus4W),.sel(Result_SrcW),.o(ResultW));
    
    //mux for PC_ Selector

    wire [31:0] address;
    mux2x1 mux2(.a(pc_targetE),.b(PCPlus4F),.sel(PC_SrcE),.o(pc_next));
    mux2x1 priority_mux(.a(address),.b(pc_next),.sel(PC_CSR),.o(pc_next1));
   //assign pc_next =  PCPlus4F; // just to avoid control hazard
   
    CSR sr(.interrupt(interrupt), .PCE(PCE), .ret(ret),.address(address), .PC_CSR(PC_CSR),.interrupt_pending(interrupt_pending));  

endmodule

module CSR (interrupt, PCE, ret, address, PC_CSR,interrupt_pending);
input interrupt, ret;
input [31:0] PCE;
output reg [31:0] address;
output reg PC_CSR;
reg [31:0] SPEC;
output reg interrupt_pending;

always @ (posedge ret) begin
//if (ret) begin
PC_CSR = 1'd1;
address = SPEC;
end
always @ (negedge ret) begin
PC_CSR =1'd0;
end
always @(posedge interrupt) begin
interrupt_pending = 1'd1;
PC_CSR = 1'd1;
SPEC = PCE;
address = 32'h28;
end

always @ (negedge interrupt) begin
PC_CSR = 1'd0;
interrupt_pending = 1'd0;
end

endmodule
module HazardUnit (Rs1E,Rs2E,ForwardAE,ForwardBE,RdM,RdW,RegWriteM,RegWriteW,ResultSrc0,RdE,Rs1D,Rs2D,StallF,StallD,FlushE,PCSrcE,FlushD,intrupt,FlushM,ret);

        input [4:0] Rs1E, Rs2E, Rs1D, Rs2D, RdE, RdM, RdW;
        input RegWriteM,RegWriteW, ResultSrc0, PCSrcE,intrupt,ret;
        output reg [1:0] ForwardAE,ForwardBE;
        output reg StallF,StallD,FlushE,FlushD,FlushM;
        reg lwStall;
        
        always @(*) begin
        if (((Rs1E == RdM) & RegWriteM) & (Rs1E != 0))
        ForwardAE = 2'b10;
        
        else if (((Rs1E == RdW) & RegWriteW) & (Rs1E != 0))
        ForwardAE = 2'b01;
        
        else 
        ForwardAE = 2'b00;
        end
        
        always @(*) begin
        if (((Rs2E == RdM) & RegWriteM) & (Rs2E != 0))
        ForwardBE = 2'b10;
        
        else if (((Rs2E == RdW) & RegWriteW) & (Rs2E != 0))
        ForwardBE = 2'b01;
        
        else 
        ForwardBE = 2'b00;
        end

        always @(*) begin
        
        lwStall = ResultSrc0 & ((Rs1D == RdE) || (Rs2D == RdE));
        
        FlushE = lwStall || PCSrcE || intrupt;
        StallD = lwStall;
        StallF = lwStall;
        
        FlushD = PCSrcE  || intrupt || ret;
        
        FlushM = intrupt;
        
        end

endmodule



//datapath ( input pc,


// A module to generate the address of next instruction
// LOGIC: 	Add 1 in program counter if its a normal instruction
//			Add address of label in PC if its a branch instruction			
// other parameters can also be added based on Datapath and Controller Inputs/Outputs
//module adress_generator (output [31:0] pc, input PC_Src, input [31:0] immext,input rst,input clk);	

//	// Write your code here. This is not the part of Phase-I
//	wire [31:0] Pc_next ,Pc_target ; 
//	always @ (posedge clk) begin
//	if (rst) begin
//	   pc = 32'h00;
//	end
//	else begin
//	adder(.a(pc),.b(32'd4),.y(Pc_next));
//	adder(.a(pc),.b(immext),.y(Pc_target));
	
//     mux2x1(.a(Pc_target),.b(Pc_next),.sel(PC_Src),.o(pc));
//	end
//endmodule


// A module that will carry the all instructions. PC value will be provided to this module and it will return the instuction
// other parameters can also be added based on Datapath and Controller Inputs/Outputs
module Instruction_Memory (input [31:0] pc,output reg [31:0] instruction);
    
    always @ (*) begin
    case(pc)                //31                   
//        32'h0000: instruction = 32'h00002403;
//        32'h0004: instruction = 32'h00102483;
//        32'h0008: instruction = 32'h00202503;
//        32'h000c: instruction = 32'h00152583;
        
        //32'h0000: instruction = 32'h00800413;//00000000110000000000010000010011;//  a = 12
        //32'h0004: instruction = 32'h00900493;//00000000100100000000010010010011;//4 b = 9
      
      //not
      //32'h0000: instruction = 32'h01900413;
      //32'h0004: instruction = 32'h01400493; 
      //32'h0008: instruction = 32'h0x40940433;
    
//    32'h0008: instruction = 32'h00A00513;//00940c63;//32'b00000000100101000000011001100011;//8
//    32'h000c: instruction = 32'h00B00593; //00944663;//32'b00000000100101000000011001010101;   //12 
//    32'h0010: instruction = 32'h00B50633;//40940433;//32'b00100000100101000000010000110011;//16
//    32'h0014: instruction = 32'h00A606B3;//ff5ff06f;//32'b11111111010111111111000011101111;//20
//    32'h0018: instruction = 32'h00068713;//408484b3;//32'b00100000100001001000010010110011;//24
//    32'h001c: instruction = 32'hFED70EE3;//fedff06f;//32'b11111111010111111111000011101111;//28
  
  
    //32'h0020: instruction = 32'hFEDA4AE3;//0000006f;//32
    //32'h0024: instruction = 32'hFEFA06E3;//36
    
    
    
    
//    32'h0   : instruction = 32'h00b00513;
//    32'h4   : instruction = 32'h00e00593;
//    32'hc   : instruction = 32'h00d00613;
//    32'h10  : instruction = 32'h01300693;
//    32'h14  : instruction = 32'h01800713;
//    32'h18  : instruction = 32'h00b569b3;
//    32'h1c  : instruction = 32'h00c59a33;
//    32'h20  : instruction = 32'h40e68ab3;
//    32'h24  : instruction = 32'h00a00513;
//    32'h28  : instruction = 32'h00c00593;
//    32'h2c  : instruction = 32'h00f00613;
//    32'h30  : instruction = 32'h01400693;
//    32'h34  : instruction = 32'h00d587b3;
//    32'h38  : instruction = 32'h00f68833;
//    32'h3c  : instruction = 32'h00a02623;
//    32'h40  : instruction = 32'h00000013;
//    32'h44  : instruction = 32'h00000013;
//    32'h48  : instruction = 32'h00000013;
//    32'h4c  : instruction = 32'h00000013;
//    32'h50  : instruction = 32'h00000013;
//    32'h54  : instruction = 32'h00c02883;
//    32'h58  : instruction = 32'h01100933;
//    32'h5c  : instruction = 32'h01700663;
//    32'h60  : instruction = 32'h016b0b13;
//    32'h64  : instruction = 32'h00000663;
//    32'h68  : instruction = 32'h01700b93;
//    32'h6c  : instruction = 32'hfe0008e3;
//    32'h70  : instruction = 32'h00000013;

    
            
//      32'h0   : instruction = 32'h01400A13;
//      32'h4   : instruction = 32'h00C00613;
//      32'h8   : instruction = 32'h00CA2023;
//      32'hc   : instruction = 32'h000A2C83;
//      32'h10   : instruction = 32'h002C8713;










32'h0   : instruction = 32'h01400A13;
32'h4   : instruction = 32'h00C00613;
32'h8   : instruction = 32'h00800093;
32'hc   : instruction = 32'h03200C93;
32'h10  : instruction = 32'h002C8713;
32'h14  : instruction = 32'h00100093;
32'h18  : instruction = 32'h00200113;
32'h1c  : instruction = 32'h00300193;
32'h20  : instruction = 32'h00400213;
32'h24  : instruction = 32'h00500293;
32'h28  : instruction = 32'h03200313;
32'h2c  : instruction = 32'h414303B3;
32'h30  : instruction = 32'h00008067;



    
    endcase
    end
	
endmodule


// This module is called Data_Memory. It will consists of 256 byte memory unit. It will have 
// one input as 8-bit address, 1 input flag wr that will decide if you want to read memory or write memory
module Data_Memory(output reg [31:0] Data_Out, input [31:0] Data_In, input [31:0] D_Addr, input wr, input clk );
		reg [31:0] Mem [255:0];			// Data Memory
  
	// Write your code here
	always @(*) begin
	Data_Out = Mem[D_Addr]; // Data Loading
	    Mem[5] = 5;
        Mem[1] = 1;
        Mem[2] = 2;
        Mem[3] = 3;
	end
	always @(negedge clk) begin // Data Storing
	if (wr)
	Mem[D_Addr] = Data_In;
	end
endmodule



// This module is called Register_Memory. It will consists of 32 registers each of 32-bits. It will have 
// one input flag wr that will decide if you want to read any register or write or update any value in register
// This module will 2 addresses and provide the data in 2 different outputs
module register_file(Port_A, Port_B, Din, Addr_A, Addr_B, Addr_Wr, wr,Hard_wired, clk); 
			output reg [31:0] Port_A, Port_B;			// Data to be provided from register to execute the instruction // reg by me
			input [31:0] Din;						// Data to be loaded in the register
			input [4:0] Addr_A, Addr_B, Addr_Wr;	// Address (or number) of register to be written or to be read
			input wr, clk;	
			output reg [31:0] Hard_wired;						// input wr flag input // by me clk
			reg [31:0] Reg_File [31:0];				// Register file

	// Write your code here
	// read
	
	always @ (*) begin  // Data Reading
	Reg_File[0] = 32'd0;
	Port_A = Reg_File[Addr_A];
	Port_B = Reg_File[Addr_B];
	Hard_wired = Reg_File[8];
	end
	
	always @(negedge clk) begin // Data Writing
	if(wr)
	   Reg_File[Addr_Wr] = Din;
	end

	
endmodule


module Control_Unit(input [6:0] op,
                    input [2:0] funct3,
                    input funct7,
                    output reg MemWrite,
                    output reg ALU_Src,
                    output reg RegWrite,
                    output reg [3:0] ALUControl,
                    output reg [1:0] Imm_Src,
                    output reg [1:0] Result_Src,
                    output reg jump, 
                    output reg branch,
                    output reg ret );			
	// This is the part of Phase-II
	
	reg [1:0] ALUOP;
	always @(*)
	begin 
	 case (op)
	 7'b0000011: //lw
	       begin
	           RegWrite   = 1'b1;
	           Imm_Src    = 2'b00;
	           ALU_Src    = 1'b1;
	           MemWrite   = 1'b0;
	           Result_Src = 2'b01;
	           branch     = 1'b0;
	           ALUOP      = 2'b00;
	           jump       = 1'b0;
	           ret       = 1'b0;
	           end
	           
      7'b0100011: //sw
              begin
              RegWrite   = 1'b0;
              Imm_Src    = 2'b01;
              ALU_Src    = 1'b1;
              MemWrite   = 1'b1;
              Result_Src = 2'bxx;
              branch     = 1'b0;
              ALUOP      = 2'b00;
              jump       = 1'b0;
              ret       = 1'b0;
               end  
      7'b0110011: //R-type
              begin
               RegWrite   = 1'b1;
               Imm_Src    = 2'bxx;
               ALU_Src    = 1'b0;
               MemWrite   = 1'b0;
               Result_Src = 2'b00;
               branch     = 1'b0;
               ALUOP      = 2'b10;
               jump       = 1'b0;
               ret       = 1'b0;
                        end
        7'b1100011: //beq
               begin
               RegWrite   = 1'b0;
               Imm_Src    = 2'b10;
               ALU_Src    = 1'b0;
               MemWrite   = 1'b0;
               Result_Src = 2'bxx;
               branch     = 1'b1;
               ALUOP      = 2'b01;
               jump       = 1'b0;
               ret       = 1'b0;
                              end
                              
                              
                              
   7'b1010101: //blt
             begin
               RegWrite   = 1'b0;
               Imm_Src    = 2'b10;
               ALU_Src    = 1'b0;
               MemWrite   = 1'b0;
               Result_Src = 2'bxx;
               branch     = 1'b1;
               ALUOP      = 2'b01;
               jump       = 1'b0;
               ret       = 1'b0;
               end                            
                              
                              
                              
                              
	     	 7'b0010011: //I-type ALU
                 begin
                 RegWrite   = 1'b1;
                 Imm_Src    = 2'b00;
                 ALU_Src    = 1'b1;
                 MemWrite   = 1'b0;
                 Result_Src = 2'b00;
                 branch     = 1'b0;
                 ALUOP      = 2'b10;
                 jump       = 1'b0;
                 ret       = 1'b0;
                              end
 7'b1101111: //jal
                  begin
                  RegWrite   = 1'b1;
                  Imm_Src    = 2'b11;
                  ALU_Src    = 1'bx;
                 MemWrite   = 1'b0;
                  Result_Src = 2'b10;
                  branch     = 1'b0;
                  ALUOP      = 2'bxx;
                 jump       = 1'b1;
                 ret       = 1'b0;
                 end
                 
                 
  7'b1100111: //jalr
                  begin
                  ret = 1'b1;
                  RegWrite   = 1'b0;
                  Imm_Src    = 2'b00;
                  ALU_Src    = 1'b0;
                 MemWrite   = 1'b0;
                  Result_Src = 2'b00;
                  branch     = 1'b0;
                  ALUOP      = 2'b00;
                 jump       = 1'b0;
                 end
 default: 
                                  begin
             RegWrite   = 1'b0;                       //   RegWrite   = 1'bx;
            Imm_Src    = 2'b00;                      //   Imm_Src    = 2'bxx;
            ALU_Src    = 1'b0;                       //   ALU_Src    = 1'bx;
             MemWrite   = 1'b0;                      //    MemWrite   = 1'bx;
            Result_Src = 2'b00;                      //   Result_Src = 2'bxx;
              branch     = 1'b0;                     //     branch     = 1'bx;
             ALUOP      = 2'b00;                     //    ALUOP      = 2'bxx;
            jump       = 1'b0;                        //  jump       = 1'bx;   
            ret       = 1'b0;                          // return
	           end
	 endcase
	 
	 case (ALUOP)
	 2'b00: ALUControl = 4'b0000;
	 
	 2'b01:
	   begin
	   case (funct3)
	   3'b000:  ALUControl = 4'b0001; // sybtract
	   3'b100:  ALUControl = 4'b1110; // less than
	   endcase
       end
	
	 2'b10: begin
	 //if ((funct3 == 3'b000 && (funct7 == 0)) begin
	   case ({funct3,funct7})
	         {3'b000,1'b0}:  ALUControl = 4'b0000;
	         {3'b000,1'b1}:  ALUControl = 4'b0001;
	         {3'b001,1'b0}:  ALUControl = 4'b0001;
	         {3'b001,1'b1}:  ALUControl = 4'b0001;
	         {3'b010,1'b0}:  ALUControl = 4'b0001;
	         {3'b010,1'b1}:  ALUControl = 4'b0001;
	         {3'b011,1'b0}:  ALUControl = 4'b0001;
	         {3'b011,1'b1}:  ALUControl = 4'b0001;
	         {3'b100,1'b1}:  ALUControl = 4'b0001;
	         {3'b101,1'b0}:  ALUControl = 4'b0001;
	         {3'b101,1'b1}:  ALUControl = 4'b0001;
	         {3'b110,1'b0}:  ALUControl = 4'b0001;
	         {3'b110,1'b1}:  ALUControl = 4'b0001;
	         {3'b111,1'b0}:  ALUControl = 4'b0001;
	         {3'b111,1'b1}:  ALUControl = 4'b0001;

	    endcase
	    end
	    default: ALUControl = 4'bxxxx;
	    endcase
	    end

endmodule






// General Module of two input (5 bit) multiplexer. This multiplexer will be connected with ALU control signals
//module mux(o,a,b, sel);
//    input [4:0] a,b;			// 5 bit inputs
//	input sel;					// selection signal
//    output reg [4:0] o;			// 5 bit output

//	// write your code here!
	
//endmodule

// A two by one 32 bit multiplexer (to select the branch instruction)
module mux2x1(output  [31:0]o,		// 32 bit output
					input[31:0]a,b,		// 32 bit inputs
					input sel			// Selection Signal
			);
			
	// Write your code here!
	assign o = sel ? a : b;
	
endmodule


module mux3x1(output [31:0]o,		// 32 bit output
					input[31:0]a,b,c,	// 32 bit inputs
					input [1:0] sel			// Selection Signal
			);
			
	// Write your code here!
	assign o = sel[1] ? c: (sel[0] ? b : a);
	
endmodule

module adder(input [31:0] a,b,output [31:0] y);
         assign y = a+b;    
endmodule 



// The final module ALU which will accept the signal (Function) from Control Unit
// and two operands (either from register file or from memory (data or address),
// will perform the desired operarion and proivde the output in Result and Zero flag.
//module ALU(Result, alu_z, Op_A, Op_B, Function);
//	output [31:0] Result;		// 32 bit Result
//	output alu_z;				// Zero flag (1 if result is zero)
//	input [31:0] Op_A, Op_B;	// Two operands based on the type of instruction
//	input [3:0] Func;			// Function to be performed as per instructed by Control Unit
	
//	// Write your code here
//endmodule


module alu(
           input [31:0] A,B,  // ALU 8-bit Inputs
           input [3:0] ALU_Sel,// ALU Selection
           output [31:0] ALU_Out, // ALU 8-bit Output
           output CarryOut, // Carry Out Flag
		   output ZeroOut	// Zero Flag
		   );
    reg [31:0] ALU_Result;
    wire [32:0] tmp;
    assign ALU_Out = ALU_Result; // ALU out
    assign tmp = {1'b0,A} + {1'b0,B};
    assign CarryOut = tmp[32]; // Carryout flag
	assign ZeroOut = (ALU_Result == 0); // Zero Flag
    always @(*)
    begin
        case(ALU_Sel)
        4'b0000: // Addition
           ALU_Result = A + B ;
        4'b0001: // Subtraction
           ALU_Result = A - B ;
        4'b0010: // Multiplication
           ALU_Result = A * B;
        4'b0011: // Division
           ALU_Result = A/B;
        4'b0100: // Logical shift left
           ALU_Result = A<<B;
         4'b0101: // Logical shift right
           ALU_Result = A>>B;
         4'b0110: // Rotate left
           ALU_Result = {A[30:0],A[31]};
         4'b0111: // Rotate right
           ALU_Result = {A[0],A[31:1]};
          4'b1000: //  Logical and
           ALU_Result = A & B;
          4'b1001: //  Logical or
           ALU_Result = A | B;
          4'b1010: //  Logical xor
           ALU_Result = A ^ B;
          4'b1011: //  Logical nor
           ALU_Result = ~(A | B);
          4'b1100: // Logical nand
           ALU_Result = ~(A & B);
          4'b1101: // Logical xnor
           ALU_Result = ~(A ^ B);
          4'b1110: // Less comparison
           ALU_Result = (A<B)?32'd0:32'd1 ;
          4'b1111: // Equal comparison
            ALU_Result = (A==B)?32'd1:32'd0 ;
          default: ALU_Result = A + B ;
        endcase
    end

endmodule


module extend(input  		[31:7] instr,
              input  		[1:0]  immsrc,
              output reg 	[31:0] immext);
    always @(*) 
    case(immsrc)
         // I−type
    2'b00:     immext = {{20{instr[31]}}, instr[31:20]};
		 // S−type (stores)
    2'b01:     immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};
         // B−type (branches)
    2'b10:      immext = {{20{instr[31]}}, instr[7],  instr[30:25], instr[11:8], 1'b0};                          // J−type (jal)
		// J−type (branches)
	2'b11:      immext = {{12{instr[31]}}, instr[19:12],  instr[20], instr[30:21], 1'b0};
           
	default: 	immext = 32'bx; // undefined
    endcase
endmodule






















