`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/20/2021 09:21:04 PM
// Design Name: 
// Module Name: test
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module test;
reg clk, rst,interrupt;

wire alu_z;						// An LED turned ON if result is zero
wire [7:0] Anode_Activate;		// Anodes to control 7-segments
wire [6:0] LED_out;	

main a1(.rst(rst),.clk(clk),.alu_z(alu_z),.Anode_Activate(Anode_Activate),.LED_out(LED_out),.interrupt(interrupt));

initial begin 
clk = 1'b1; rst = 1; interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 1;
#5 clk = 1'b0;#5 rst = 0;interrupt = 1;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 clk = 1'b0;#5 rst = 0;interrupt = 0;
#5 clk = 1'b1;#5 rst = 0;interrupt = 0;
#5 $stop;
end

endmodule
