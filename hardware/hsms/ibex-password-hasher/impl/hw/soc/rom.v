`timescale 1 ns / 1 ps

module rom #(
    parameter ADDR_BITS = 10,
    parameter FILENAME = "rom.mem"
) (
    input clk,

    input valid1,
    input [31:0] addr1,
    output [31:0] dout1,
    output ready1,

    input valid2,
    input [31:0] addr2,
    output [31:0] dout2,
    output ready2
);

reg [31:0] rom [(2**(ADDR_BITS-2))-1:0];

// note: with Yosys, need to read this file in with `-defer` for the
// parameter to work
// see
// https://www.reddit.com/r/yosys/comments/f92bke/whats_the_right_way_to_load_a_verilog_module_that/
`ifndef ROSETTE
initial begin
    $readmemh(FILENAME, rom);
end
`endif

// workaround to make Yosys output better
wire [ADDR_BITS-3:0] xaddr;
assign xaddr = 0;
always @(posedge clk) begin
    rom[xaddr] <= rom[xaddr];
end

wire [ADDR_BITS-3:0] idx1 = addr1[ADDR_BITS-1:2];
assign dout1 = rom[idx1];
assign ready1 = valid1; // always ready

wire [ADDR_BITS-3:0] idx2 = addr2[ADDR_BITS-1:2];
assign dout2 = rom[idx2];
assign ready2 = valid2; // always ready

endmodule
