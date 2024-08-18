module hsm (
	clk,
	resetn,
	rx,
	cts,
	tx,
	rts
);
	parameter FIRMWARE_FILE = "fw/firmware.mem";
	parameter ROM_ADDR_BITS = 17;
	parameter RAM_ADDR_BITS = 12;
	parameter FRAM_ADDR_BITS = 12;
	input clk;
	input resetn;
	input rx;
	input cts;
	output wire tx;
	output wire rts;
	wrapper #(
		.FIRMWARE_FILE(FIRMWARE_FILE),
		.ROM_ADDR_BITS(ROM_ADDR_BITS),
		.RAM_ADDR_BITS(RAM_ADDR_BITS),
		.FRAM_ADDR_BITS(FRAM_ADDR_BITS)
	) wrapper(
		.clk(clk),
		.resetn(resetn),
		.uart_tx(tx),
		.uart_rx(rx),
		.uart_cts(cts),
		.uart_rts(rts)
	);
endmodule
module fram (
	clk,
	resetn,
	valid,
	addr,
	din,
	wstrb,
	dout,
	ready
);
	parameter ADDR_BITS = 10;
	input clk;
	input resetn;
	input valid;
	input [31:0] addr;
	input [31:0] din;
	input [3:0] wstrb;
	output wire [31:0] dout;
	output wire ready;
	wire [ADDR_BITS - 3:0] idx = addr[ADDR_BITS - 1:2];
	reg [31:0] fram [(2 ** (ADDR_BITS - 2)) - 1:0];
	wire [31:0] din_masked = {(wstrb[3] ? din[31:24] : fram[idx][31:24]), (wstrb[2] ? din[23:16] : fram[idx][23:16]), (wstrb[1] ? din[15:8] : fram[idx][15:8]), (wstrb[0] ? din[7:0] : fram[idx][7:0])};
	always @(posedge clk)
		if ((resetn && valid) && (wstrb != 4'b0000))
			fram[idx] <= din_masked;
	assign dout = fram[idx];
	assign ready = valid;
endmodule
module simpleuart (
	clk,
	resetn,
	ser_tx,
	ser_rx,
	ser_rts,
	reg_div_we,
	reg_div_di,
	reg_div_do,
	reg_dat_we,
	reg_dat_re,
	reg_dat_di,
	reg_dat_do,
	reg_dat_wait,
	reg_send_busy
);
	parameter integer DEFAULT_DIV = 1;
	input clk;
	input resetn;
	output wire ser_tx;
	input ser_rx;
	output wire ser_rts;
	input [3:0] reg_div_we;
	input [31:0] reg_div_di;
	output wire [31:0] reg_div_do;
	input reg_dat_we;
	input reg_dat_re;
	input [31:0] reg_dat_di;
	output wire [31:0] reg_dat_do;
	output wire reg_dat_wait;
	output wire reg_send_busy;
	reg [31:0] cfg_divider;
	reg [3:0] recv_state;
	reg [31:0] recv_divcnt;
	reg [7:0] recv_pattern;
	reg [7:0] recv_buf_data;
	reg recv_buf_valid;
	reg [9:0] send_pattern;
	reg [3:0] send_bitcnt;
	reg [31:0] send_divcnt;
	reg send_dummy;
	reg initialized;
	assign reg_div_do = cfg_divider;
	assign reg_dat_wait = reg_dat_we && ((send_bitcnt != 4'h0) || send_dummy);
	assign reg_dat_do = (recv_buf_valid ? {24'h000000, recv_buf_data} : ~0);
	assign reg_send_busy = send_bitcnt != 4'h0;
	always @(posedge clk)
		if (!resetn) begin
			cfg_divider <= DEFAULT_DIV;
			initialized <= 0;
		end
		else begin
			if (reg_div_we[0])
				cfg_divider[7:0] <= reg_div_di[7:0];
			if (reg_div_we[1])
				cfg_divider[15:8] <= reg_div_di[15:8];
			if (reg_div_we[2])
				cfg_divider[23:16] <= reg_div_di[23:16];
			if (reg_div_we[3])
				cfg_divider[31:24] <= reg_div_di[31:24];
			if (|reg_div_we)
				initialized <= 1;
		end
	assign ser_rts = !initialized || recv_buf_valid;
	always @(posedge clk)
		if (!resetn || !initialized) begin
			recv_state <= 0;
			recv_divcnt <= 0;
			recv_pattern <= 0;
			recv_buf_data <= 0;
			recv_buf_valid <= 0;
		end
		else begin
			recv_divcnt <= recv_divcnt + 1;
			if (reg_dat_re)
				recv_buf_valid <= 0;
			case (recv_state)
				0: begin
					if (!ser_rx) begin
						if (cfg_divider == 32'h00000001) begin
							recv_state <= 2;
							recv_pattern <= 0;
						end
						else
							recv_state <= 1;
					end
					recv_divcnt <= 1;
				end
				1:
					if ((2 * recv_divcnt) >= cfg_divider) begin
						recv_state <= 2;
						recv_divcnt <= 0;
						recv_pattern <= 0;
					end
				10:
					if ((recv_divcnt + 1) >= cfg_divider) begin
						recv_buf_data <= recv_pattern;
						recv_buf_valid <= 1;
						recv_state <= 0;
					end
				default:
					if ((recv_divcnt + 1) >= cfg_divider) begin
						recv_pattern <= {ser_rx, recv_pattern[7:1]};
						recv_state <= recv_state + 1;
						recv_divcnt <= 0;
					end
			endcase
		end
	assign ser_tx = send_pattern[0];
	always @(posedge clk) begin
		if (|reg_div_we)
			send_dummy <= 1;
		send_divcnt <= send_divcnt + 1;
		if (!resetn || !initialized) begin
			send_pattern <= ~0;
			send_bitcnt <= 0;
			send_divcnt <= 0;
			send_dummy <= 0;
		end
		else if (send_dummy && (send_bitcnt == 4'h0)) begin
			send_pattern <= ~0;
			send_bitcnt <= 15;
			send_divcnt <= 0;
			send_dummy <= 0;
		end
		else if (reg_dat_we && (send_bitcnt == 4'h0)) begin
			send_pattern <= {1'b1, reg_dat_di[7:0], 1'b0};
			send_bitcnt <= 10;
			send_divcnt <= 0;
		end
		else if (((send_divcnt + 1) >= cfg_divider) && (send_bitcnt != 4'h0)) begin
			send_pattern <= {1'b1, send_pattern[9:1]};
			send_bitcnt <= send_bitcnt - 1;
			send_divcnt <= 0;
		end
	end
endmodule
module wrapper (
	clk,
	resetn,
	uart_rx,
	uart_cts,
	uart_tx,
	uart_rts
);
	parameter FIRMWARE_FILE = "firmware.mem";
	parameter ROM_ADDR_BITS = 12;
	parameter RAM_ADDR_BITS = 17;
	parameter FRAM_ADDR_BITS = 20;
	input clk;
	input resetn;
	input uart_rx;
	input uart_cts;
	output wire uart_tx;
	output wire uart_rts;
	localparam pwrmgr_state_embryo = 2'b01;
	localparam pwrmgr_state_running = 2'b10;
	reg [1:0] pwrmgr_state;
	wire soc_resetn;
	wire poweroff_rq;
	assign soc_resetn = (resetn && (pwrmgr_state != pwrmgr_state_embryo)) && !((pwrmgr_state == pwrmgr_state_running) && poweroff_rq);
	always @(posedge clk)
		if (!resetn)
			pwrmgr_state <= pwrmgr_state_embryo;
		else if (pwrmgr_state == pwrmgr_state_embryo) begin
			if (!uart_cts)
				pwrmgr_state <= pwrmgr_state_running;
		end
		else if (pwrmgr_state == pwrmgr_state_running) begin
			if (poweroff_rq)
				pwrmgr_state <= pwrmgr_state_embryo;
		end
	wire soc_tx;
	wire soc_rts;
	assign uart_tx = (pwrmgr_state == pwrmgr_state_running ? soc_tx : 1);
	assign uart_rts = (pwrmgr_state == pwrmgr_state_running ? soc_rts : 1);
	soc #(
		.FIRMWARE_FILE(FIRMWARE_FILE),
		.ROM_ADDR_BITS(ROM_ADDR_BITS),
		.RAM_ADDR_BITS(RAM_ADDR_BITS),
		.FRAM_ADDR_BITS(FRAM_ADDR_BITS)
	) soc(
		.clk(clk),
		.resetn(soc_resetn),
		.uart_tx(soc_tx),
		.uart_rx(uart_rx),
		.uart_cts(uart_cts),
		.uart_rts(soc_rts),
		.poweroff_rq(poweroff_rq)
	);
endmodule
module ram (
	clk,
	resetn,
	valid,
	addr,
	din,
	wstrb,
	dout,
	ready
);
	parameter ADDR_BITS = 10;
	input clk;
	input resetn;
	input valid;
	input [31:0] addr;
	input [31:0] din;
	input [3:0] wstrb;
	output wire [31:0] dout;
	output wire ready;
	wire [ADDR_BITS - 3:0] idx = addr[ADDR_BITS - 1:2];
	reg [31:0] ram [(2 ** (ADDR_BITS - 2)) - 1:0];
	wire [31:0] din_masked = {(wstrb[3] ? din[31:24] : ram[idx][31:24]), (wstrb[2] ? din[23:16] : ram[idx][23:16]), (wstrb[1] ? din[15:8] : ram[idx][15:8]), (wstrb[0] ? din[7:0] : ram[idx][7:0])};
	always @(posedge clk)
		if ((resetn && valid) && (wstrb != 4'b0000))
			ram[idx] <= din_masked;
	assign dout = ram[idx];
	assign ready = valid;
endmodule
module ibex_lockstep (
	clk_i,
	rst_ni,
	hart_id_i,
	boot_addr_i,
	instr_req_i,
	instr_gnt_i,
	instr_rvalid_i,
	instr_addr_i,
	instr_rdata_i,
	instr_err_i,
	data_req_i,
	data_gnt_i,
	data_rvalid_i,
	data_we_i,
	data_be_i,
	data_addr_i,
	data_wdata_i,
	data_rdata_i,
	data_err_i,
	dummy_instr_id_i,
	dummy_instr_wb_i,
	rf_raddr_a_i,
	rf_raddr_b_i,
	rf_waddr_wb_i,
	rf_we_wb_i,
	rf_wdata_wb_ecc_i,
	rf_rdata_a_ecc_i,
	rf_rdata_b_ecc_i,
	ic_tag_req_i,
	ic_tag_write_i,
	ic_tag_addr_i,
	ic_tag_wdata_i,
	ic_tag_rdata_i,
	ic_data_req_i,
	ic_data_write_i,
	ic_data_addr_i,
	ic_data_wdata_i,
	ic_data_rdata_i,
	ic_scr_key_valid_i,
	ic_scr_key_req_i,
	irq_software_i,
	irq_timer_i,
	irq_external_i,
	irq_fast_i,
	irq_nm_i,
	irq_pending_i,
	debug_req_i,
	crash_dump_i,
	double_fault_seen_i,
	fetch_enable_i,
	alert_minor_o,
	alert_major_internal_o,
	alert_major_bus_o,
	core_busy_i,
	test_en_i,
	scan_rst_ni
);
	parameter [31:0] LockstepOffset = 2;
	parameter [0:0] PMPEnable = 1'b0;
	parameter [31:0] PMPGranularity = 0;
	parameter [31:0] PMPNumRegions = 4;
	parameter [31:0] MHPMCounterNum = 0;
	parameter [31:0] MHPMCounterWidth = 40;
	parameter [0:0] RV32E = 1'b0;
	parameter integer RV32M = 32'sd2;
	parameter integer RV32B = 32'sd0;
	parameter [0:0] BranchTargetALU = 1'b0;
	parameter [0:0] WritebackStage = 1'b0;
	parameter [0:0] ICache = 1'b0;
	parameter [0:0] ICacheECC = 1'b0;
	localparam [31:0] ibex_pkg_BUS_SIZE = 32;
	parameter [31:0] BusSizeECC = ibex_pkg_BUS_SIZE;
	localparam [31:0] ibex_pkg_ADDR_W = 32;
	localparam [31:0] ibex_pkg_IC_LINE_SIZE = 64;
	localparam [31:0] ibex_pkg_IC_LINE_BYTES = 8;
	localparam [31:0] ibex_pkg_IC_NUM_WAYS = 2;
	localparam [31:0] ibex_pkg_IC_SIZE_BYTES = 4096;
	localparam [31:0] ibex_pkg_IC_NUM_LINES = (ibex_pkg_IC_SIZE_BYTES / ibex_pkg_IC_NUM_WAYS) / ibex_pkg_IC_LINE_BYTES;
	localparam [31:0] ibex_pkg_IC_INDEX_W = $clog2(ibex_pkg_IC_NUM_LINES);
	localparam [31:0] ibex_pkg_IC_LINE_W = 3;
	localparam [31:0] ibex_pkg_IC_TAG_SIZE = ((ibex_pkg_ADDR_W - ibex_pkg_IC_INDEX_W) - ibex_pkg_IC_LINE_W) + 1;
	parameter [31:0] TagSizeECC = ibex_pkg_IC_TAG_SIZE;
	parameter [31:0] LineSizeECC = ibex_pkg_IC_LINE_SIZE;
	parameter [0:0] BranchPredictor = 1'b0;
	parameter [0:0] DbgTriggerEn = 1'b0;
	parameter [31:0] DbgHwBreakNum = 1;
	parameter [0:0] ResetAll = 1'b0;
	localparam signed [31:0] ibex_pkg_LfsrWidth = 32;
	localparam [31:0] ibex_pkg_RndCnstLfsrSeedDefault = 32'hac533bf4;
	parameter [31:0] RndCnstLfsrSeed = ibex_pkg_RndCnstLfsrSeedDefault;
	localparam [159:0] ibex_pkg_RndCnstLfsrPermDefault = 160'h1e35ecba467fd1b12e958152c04fa43878a8daed;
	parameter [159:0] RndCnstLfsrPerm = ibex_pkg_RndCnstLfsrPermDefault;
	parameter [0:0] SecureIbex = 1'b0;
	parameter [0:0] DummyInstructions = 1'b0;
	parameter [0:0] RegFileECC = 1'b0;
	parameter [31:0] RegFileDataWidth = 32;
	parameter [0:0] MemECC = 1'b0;
	parameter [31:0] MemDataWidth = (MemECC ? 39 : 32);
	parameter [31:0] DmHaltAddr = 32'h1a110800;
	parameter [31:0] DmExceptionAddr = 32'h1a110808;
	input wire clk_i;
	input wire rst_ni;
	input wire [31:0] hart_id_i;
	input wire [31:0] boot_addr_i;
	input wire instr_req_i;
	input wire instr_gnt_i;
	input wire instr_rvalid_i;
	input wire [31:0] instr_addr_i;
	input wire [MemDataWidth - 1:0] instr_rdata_i;
	input wire instr_err_i;
	input wire data_req_i;
	input wire data_gnt_i;
	input wire data_rvalid_i;
	input wire data_we_i;
	input wire [3:0] data_be_i;
	input wire [31:0] data_addr_i;
	input wire [MemDataWidth - 1:0] data_wdata_i;
	input wire [MemDataWidth - 1:0] data_rdata_i;
	input wire data_err_i;
	input wire dummy_instr_id_i;
	input wire dummy_instr_wb_i;
	input wire [4:0] rf_raddr_a_i;
	input wire [4:0] rf_raddr_b_i;
	input wire [4:0] rf_waddr_wb_i;
	input wire rf_we_wb_i;
	input wire [RegFileDataWidth - 1:0] rf_wdata_wb_ecc_i;
	input wire [RegFileDataWidth - 1:0] rf_rdata_a_ecc_i;
	input wire [RegFileDataWidth - 1:0] rf_rdata_b_ecc_i;
	input wire [1:0] ic_tag_req_i;
	input wire ic_tag_write_i;
	input wire [ibex_pkg_IC_INDEX_W - 1:0] ic_tag_addr_i;
	input wire [TagSizeECC - 1:0] ic_tag_wdata_i;
	input wire [(ibex_pkg_IC_NUM_WAYS * TagSizeECC) - 1:0] ic_tag_rdata_i;
	input wire [1:0] ic_data_req_i;
	input wire ic_data_write_i;
	input wire [ibex_pkg_IC_INDEX_W - 1:0] ic_data_addr_i;
	input wire [LineSizeECC - 1:0] ic_data_wdata_i;
	input wire [(ibex_pkg_IC_NUM_WAYS * LineSizeECC) - 1:0] ic_data_rdata_i;
	input wire ic_scr_key_valid_i;
	input wire ic_scr_key_req_i;
	input wire irq_software_i;
	input wire irq_timer_i;
	input wire irq_external_i;
	input wire [14:0] irq_fast_i;
	input wire irq_nm_i;
	input wire irq_pending_i;
	input wire debug_req_i;
	input wire [159:0] crash_dump_i;
	input wire double_fault_seen_i;
	input wire [3:0] fetch_enable_i;
	output wire alert_minor_o;
	output wire alert_major_internal_o;
	output wire alert_major_bus_o;
	input wire [3:0] core_busy_i;
	input wire test_en_i;
	input wire scan_rst_ni;
	localparam [31:0] LockstepOffsetW = $clog2(LockstepOffset);
	localparam [31:0] OutputsOffset = LockstepOffset + 1;
	wire [LockstepOffsetW - 1:0] rst_shadow_cnt_d;
	reg [LockstepOffsetW - 1:0] rst_shadow_cnt_q;
	wire [LockstepOffsetW - 1:0] rst_shadow_cnt_incr;
	wire rst_shadow_set_d;
	wire rst_shadow_set_q;
	wire rst_shadow_n;
	reg enable_cmp_q;
	assign rst_shadow_cnt_incr = rst_shadow_cnt_q + 1'b1;
	function automatic [LockstepOffsetW - 1:0] sv2v_cast_3B624;
		input reg [LockstepOffsetW - 1:0] inp;
		sv2v_cast_3B624 = inp;
	endfunction
	assign rst_shadow_set_d = rst_shadow_cnt_q == sv2v_cast_3B624(LockstepOffset - 1);
	assign rst_shadow_cnt_d = (rst_shadow_set_d ? rst_shadow_cnt_q : rst_shadow_cnt_incr);
	always @(posedge clk_i)
		if (!rst_ni) begin
			rst_shadow_cnt_q <= 1'sb0;
			enable_cmp_q <= 1'sb0;
		end
		else begin
			rst_shadow_cnt_q <= rst_shadow_cnt_d;
			enable_cmp_q <= rst_shadow_set_q;
		end
	prim_flop #(
		.Width(1),
		.ResetValue(1'b0)
	) u_prim_rst_shadow_set_flop(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.d_i(rst_shadow_set_d),
		.q_o(rst_shadow_set_q)
	);
	prim_clock_mux2 #(.NoFpgaBufG(1'b1)) u_prim_rst_shadow_n_mux2(
		.clk0_i(rst_shadow_set_q),
		.clk1_i(scan_rst_ni),
		.sel_i(test_en_i),
		.clk_o(rst_shadow_n)
	);
	reg [((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? (LockstepOffset * (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25)) - 1 : (LockstepOffset * (1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24))) + (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 23)):((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24)] shadow_inputs_q;
	wire [((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24:0] shadow_inputs_in;
	reg [(LockstepOffset * TagSizeECC) - 1:0] shadow_tag_rdata_q [0:1];
	reg [(LockstepOffset * LineSizeECC) - 1:0] shadow_data_rdata_q [0:1];
	assign shadow_inputs_in[2 + (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))] = instr_gnt_i;
	assign shadow_inputs_in[1 + (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))] = instr_rvalid_i;
	assign shadow_inputs_in[MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))-:((MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))) >= (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 25))))) ? ((MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))) - (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 25)))))) + 1 : ((3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 25))))) - (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))) + 1)] = instr_rdata_i;
	assign shadow_inputs_in[3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))] = instr_err_i;
	assign shadow_inputs_in[2 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))] = data_gnt_i;
	assign shadow_inputs_in[1 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))] = data_rvalid_i;
	assign shadow_inputs_in[MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))-:((MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))) >= (1 + (RegFileDataWidth + (RegFileDataWidth + 25))) ? ((MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))) - (1 + (RegFileDataWidth + (RegFileDataWidth + 25)))) + 1 : ((1 + (RegFileDataWidth + (RegFileDataWidth + 25))) - (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))) + 1)] = data_rdata_i;
	assign shadow_inputs_in[1 + (RegFileDataWidth + (RegFileDataWidth + 24))] = data_err_i;
	assign shadow_inputs_in[RegFileDataWidth + (RegFileDataWidth + 24)-:((RegFileDataWidth + (RegFileDataWidth + 24)) >= (RegFileDataWidth + 25) ? ((RegFileDataWidth + (RegFileDataWidth + 24)) - (RegFileDataWidth + 25)) + 1 : ((RegFileDataWidth + 25) - (RegFileDataWidth + (RegFileDataWidth + 24))) + 1)] = rf_rdata_a_ecc_i;
	assign shadow_inputs_in[RegFileDataWidth + 24-:((RegFileDataWidth + 24) >= 25 ? RegFileDataWidth + 0 : 26 - (RegFileDataWidth + 24))] = rf_rdata_b_ecc_i;
	assign shadow_inputs_in[24] = irq_software_i;
	assign shadow_inputs_in[23] = irq_timer_i;
	assign shadow_inputs_in[22] = irq_external_i;
	assign shadow_inputs_in[21-:15] = irq_fast_i;
	assign shadow_inputs_in[6] = irq_nm_i;
	assign shadow_inputs_in[5] = debug_req_i;
	assign shadow_inputs_in[4-:4] = fetch_enable_i;
	assign shadow_inputs_in[0] = ic_scr_key_valid_i;
	function automatic [((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25 : 1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24)) - 1:0] sv2v_cast_6AC9E;
		input reg [((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25 : 1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24)) - 1:0] inp;
		sv2v_cast_6AC9E = inp;
	endfunction
	function automatic [TagSizeECC - 1:0] sv2v_cast_BD0FC;
		input reg [TagSizeECC - 1:0] inp;
		sv2v_cast_BD0FC = inp;
	endfunction
	function automatic [LineSizeECC - 1:0] sv2v_cast_F09E7;
		input reg [LineSizeECC - 1:0] inp;
		sv2v_cast_F09E7 = inp;
	endfunction
	always @(posedge clk_i)
		if (!rst_ni) begin : sv2v_autoblock_1
			reg [31:0] i;
			for (i = 0; i < LockstepOffset; i = i + 1)
				begin
					shadow_inputs_q[((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) + (i * ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25 : 1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24)))+:((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25 : 1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24))] <= sv2v_cast_6AC9E(1'sb0);
					shadow_tag_rdata_q[i] <= {LockstepOffset {sv2v_cast_BD0FC(0)}};
					shadow_data_rdata_q[i] <= {LockstepOffset {sv2v_cast_F09E7(0)}};
				end
		end
		else begin
			begin : sv2v_autoblock_2
				reg [31:0] i;
				for (i = 0; i < (LockstepOffset - 1); i = i + 1)
					begin
						shadow_inputs_q[((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) + (i * ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25 : 1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24)))+:((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25 : 1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24))] <= shadow_inputs_q[((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) + ((i + 1) * ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25 : 1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24)))+:((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25 : 1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24))];
						shadow_tag_rdata_q[i] <= shadow_tag_rdata_q[i + 1];
						shadow_data_rdata_q[i] <= shadow_data_rdata_q[i + 1];
					end
			end
			shadow_inputs_q[((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) + ((LockstepOffset - 1) * ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25 : 1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24)))+:((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 25 : 1 - (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24))] <= shadow_inputs_in;
			shadow_tag_rdata_q[LockstepOffset - 1] <= ic_tag_rdata_i;
			shadow_data_rdata_q[LockstepOffset - 1] <= ic_data_rdata_i;
		end
	reg [(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? (OutputsOffset * ((((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 167)) - 1 : (OutputsOffset * (1 - ((((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166))) + ((((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 165)):(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? 0 : (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166)] core_outputs_q;
	wire [(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166:0] core_outputs_in;
	wire [(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166:0] shadow_outputs_d;
	reg [(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166:0] shadow_outputs_q;
	assign core_outputs_in[71 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))] = instr_req_i;
	assign core_outputs_in[70 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))-:((70 + (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) >= (38 + (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) ? ((70 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))) - (38 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))))) + 1 : ((38 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))))) - (70 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))))) + 1)] = instr_addr_i;
	assign core_outputs_in[38 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))] = data_req_i;
	assign core_outputs_in[37 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))] = data_we_i;
	assign core_outputs_in[36 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))-:((36 + (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) >= (32 + (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) ? ((36 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))) - (32 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))))) + 1 : ((32 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))))) - (36 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))))) + 1)] = data_be_i;
	assign core_outputs_in[32 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))-:((32 + (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) >= (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))) ? ((32 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))) - (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))))) + 1 : ((MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))) - (32 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))))) + 1)] = data_addr_i;
	assign core_outputs_in[MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))-:((MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))) >= (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) ? ((MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))) - (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))) + 1 : ((18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) - (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))) + 1)] = data_wdata_i;
	assign core_outputs_in[18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))] = dummy_instr_id_i;
	assign core_outputs_in[17 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))] = dummy_instr_wb_i;
	assign core_outputs_in[16 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))-:((16 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))) >= (11 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) ? ((16 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) - (11 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))) + 1 : ((11 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) - (16 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))) + 1)] = rf_raddr_a_i;
	assign core_outputs_in[11 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))-:((11 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))) >= (6 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) ? ((11 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) - (6 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))) + 1 : ((6 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) - (11 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))) + 1)] = rf_raddr_b_i;
	assign core_outputs_in[6 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))-:((6 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))) >= (1 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) ? ((6 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) - (1 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))) + 1 : ((1 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) - (6 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))) + 1)] = rf_waddr_wb_i;
	assign core_outputs_in[1 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))] = rf_we_wb_i;
	assign core_outputs_in[RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))-:((RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))) >= (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))) ? ((RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))) - (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))) + 1 : ((ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) - (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) + 1)] = rf_wdata_wb_ecc_i;
	assign core_outputs_in[ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))-:((3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))) >= (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))) ? ((ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))) - (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) + 1 : ((1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))) - (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))) + 1)] = ic_tag_req_i;
	assign core_outputs_in[1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))] = ic_tag_write_i;
	assign core_outputs_in[ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))-:((ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))) >= (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))) ? ((ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))) - (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))) + 1 : ((TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))) - (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))) + 1)] = ic_tag_addr_i;
	assign core_outputs_in[TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))-:((TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))) >= (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))) ? ((TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))) - (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))) + 1 : ((ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))) - (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))) + 1)] = ic_tag_wdata_i;
	assign core_outputs_in[ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))-:((3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))) >= (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))) ? ((ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))) - (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))) + 1 : ((1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))) - (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))) + 1)] = ic_data_req_i;
	assign core_outputs_in[1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))] = ic_data_write_i;
	assign core_outputs_in[ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)-:((ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)) >= (LineSizeECC + 167) ? ((ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)) - (LineSizeECC + 167)) + 1 : ((LineSizeECC + 167) - (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))) + 1)] = ic_data_addr_i;
	assign core_outputs_in[LineSizeECC + 166-:((LineSizeECC + 166) >= 167 ? LineSizeECC + 0 : 168 - (LineSizeECC + 166))] = ic_data_wdata_i;
	assign core_outputs_in[166] = ic_scr_key_req_i;
	assign core_outputs_in[165] = irq_pending_i;
	assign core_outputs_in[164-:160] = crash_dump_i;
	assign core_outputs_in[4] = double_fault_seen_i;
	assign core_outputs_in[3-:4] = core_busy_i;
	always @(posedge clk_i) begin
		begin : sv2v_autoblock_3
			reg [31:0] i;
			for (i = 0; i < (OutputsOffset - 1); i = i + 1)
				core_outputs_q[(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? 0 : (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) + (i * (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 167 : 1 - ((((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166)))+:(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 167 : 1 - ((((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166))] <= core_outputs_q[(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? 0 : (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) + ((i + 1) * (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 167 : 1 - ((((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166)))+:(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 167 : 1 - ((((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166))];
		end
		core_outputs_q[(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? 0 : (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) + ((OutputsOffset - 1) * (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 167 : 1 - ((((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166)))+:(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 167 : 1 - ((((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166))] <= core_outputs_in;
	end
	wire shadow_alert_minor;
	wire shadow_alert_major_internal;
	wire shadow_alert_major_bus;
	ibex_core #(
		.PMPEnable(PMPEnable),
		.PMPGranularity(PMPGranularity),
		.PMPNumRegions(PMPNumRegions),
		.MHPMCounterNum(MHPMCounterNum),
		.MHPMCounterWidth(MHPMCounterWidth),
		.RV32E(RV32E),
		.RV32M(RV32M),
		.RV32B(RV32B),
		.BranchTargetALU(BranchTargetALU),
		.ICache(ICache),
		.ICacheECC(ICacheECC),
		.BusSizeECC(BusSizeECC),
		.TagSizeECC(TagSizeECC),
		.LineSizeECC(LineSizeECC),
		.BranchPredictor(BranchPredictor),
		.DbgTriggerEn(DbgTriggerEn),
		.DbgHwBreakNum(DbgHwBreakNum),
		.WritebackStage(WritebackStage),
		.ResetAll(ResetAll),
		.RndCnstLfsrSeed(RndCnstLfsrSeed),
		.RndCnstLfsrPerm(RndCnstLfsrPerm),
		.SecureIbex(SecureIbex),
		.DummyInstructions(DummyInstructions),
		.RegFileECC(RegFileECC),
		.RegFileDataWidth(RegFileDataWidth),
		.MemECC(MemECC),
		.MemDataWidth(MemDataWidth),
		.DmHaltAddr(DmHaltAddr),
		.DmExceptionAddr(DmExceptionAddr)
	) u_shadow_core(
		.clk_i(clk_i),
		.rst_ni(rst_shadow_n),
		.hart_id_i(hart_id_i),
		.boot_addr_i(boot_addr_i),
		.instr_req_o(shadow_outputs_d[71 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))]),
		.instr_gnt_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 2 + (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (2 + (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))))]),
		.instr_rvalid_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 1 + (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (1 + (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))))]),
		.instr_addr_o(shadow_outputs_d[70 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))-:((70 + (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) >= (38 + (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) ? ((70 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))) - (38 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))))) + 1 : ((38 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))))) - (70 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))))) + 1)]),
		.instr_rdata_i(shadow_inputs_q[((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))) : ((0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))))) + ((MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))) >= (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 25))))) ? ((MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))) - (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 25)))))) + 1 : ((3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 25))))) - (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))) + 1)) - 1)-:((MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))) >= (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 25))))) ? ((MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))) - (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 25)))))) + 1 : ((3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 25))))) - (MemDataWidth + (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))) + 1)]),
		.instr_err_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (3 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))]),
		.data_req_o(shadow_outputs_d[38 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))]),
		.data_gnt_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 2 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (2 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))]),
		.data_rvalid_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 1 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (1 + (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))))]),
		.data_we_o(shadow_outputs_d[37 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))]),
		.data_be_o(shadow_outputs_d[36 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))-:((36 + (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) >= (32 + (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) ? ((36 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))) - (32 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))))) + 1 : ((32 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))))) - (36 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))))) + 1)]),
		.data_addr_o(shadow_outputs_d[32 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))-:((32 + (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) >= (MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))) ? ((32 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))) - (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))))) + 1 : ((MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))) - (32 + (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))))) + 1)]),
		.data_wdata_o(shadow_outputs_d[MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))-:((MemDataWidth + (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))) >= (18 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) ? ((MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))) - (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))) + 1 : ((18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) - (MemDataWidth + (18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))))) + 1)]),
		.data_rdata_i(shadow_inputs_q[((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))) : ((0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))))) + ((MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))) >= (1 + (RegFileDataWidth + (RegFileDataWidth + 25))) ? ((MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))) - (1 + (RegFileDataWidth + (RegFileDataWidth + 25)))) + 1 : ((1 + (RegFileDataWidth + (RegFileDataWidth + 25))) - (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))) + 1)) - 1)-:((MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))) >= (1 + (RegFileDataWidth + (RegFileDataWidth + 25))) ? ((MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24)))) - (1 + (RegFileDataWidth + (RegFileDataWidth + 25)))) + 1 : ((1 + (RegFileDataWidth + (RegFileDataWidth + 25))) - (MemDataWidth + (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))) + 1)]),
		.data_err_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 1 + (RegFileDataWidth + (RegFileDataWidth + 24)) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (1 + (RegFileDataWidth + (RegFileDataWidth + 24))))]),
		.dummy_instr_id_o(shadow_outputs_d[18 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))]),
		.dummy_instr_wb_o(shadow_outputs_d[17 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))]),
		.rf_raddr_a_o(shadow_outputs_d[16 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))-:((16 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))) >= (11 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) ? ((16 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) - (11 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))) + 1 : ((11 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) - (16 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))) + 1)]),
		.rf_raddr_b_o(shadow_outputs_d[11 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))-:((11 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))) >= (6 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) ? ((11 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) - (6 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))) + 1 : ((6 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) - (11 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))) + 1)]),
		.rf_waddr_wb_o(shadow_outputs_d[6 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))-:((6 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))) >= (1 + (RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) ? ((6 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) - (1 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))))) + 1 : ((1 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))))) - (6 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))))) + 1)]),
		.rf_we_wb_o(shadow_outputs_d[1 + (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))]),
		.rf_wdata_wb_ecc_o(shadow_outputs_d[RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))-:((RegFileDataWidth + (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))) >= (3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))) ? ((RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))) - (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))))) + 1 : ((ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) - (RegFileDataWidth + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))))) + 1)]),
		.rf_rdata_a_ecc_i(shadow_inputs_q[((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? RegFileDataWidth + (RegFileDataWidth + 24) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (RegFileDataWidth + (RegFileDataWidth + 24))) : ((0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? RegFileDataWidth + (RegFileDataWidth + 24) : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (RegFileDataWidth + (RegFileDataWidth + 24)))) + ((RegFileDataWidth + (RegFileDataWidth + 24)) >= (RegFileDataWidth + 25) ? ((RegFileDataWidth + (RegFileDataWidth + 24)) - (RegFileDataWidth + 25)) + 1 : ((RegFileDataWidth + 25) - (RegFileDataWidth + (RegFileDataWidth + 24))) + 1)) - 1)-:((RegFileDataWidth + (RegFileDataWidth + 24)) >= (RegFileDataWidth + 25) ? ((RegFileDataWidth + (RegFileDataWidth + 24)) - (RegFileDataWidth + 25)) + 1 : ((RegFileDataWidth + 25) - (RegFileDataWidth + (RegFileDataWidth + 24))) + 1)]),
		.rf_rdata_b_ecc_i(shadow_inputs_q[((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? RegFileDataWidth + 24 : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (RegFileDataWidth + 24)) : ((0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? RegFileDataWidth + 24 : (((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) - (RegFileDataWidth + 24))) + ((RegFileDataWidth + 24) >= 25 ? RegFileDataWidth + 0 : 26 - (RegFileDataWidth + 24))) - 1)-:((RegFileDataWidth + 24) >= 25 ? RegFileDataWidth + 0 : 26 - (RegFileDataWidth + 24))]),
		.ic_tag_req_o(shadow_outputs_d[ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))-:((3 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))) >= (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))) ? ((ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))))) - (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))))) + 1 : ((1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))))) - (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))))) + 1)]),
		.ic_tag_write_o(shadow_outputs_d[1 + (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))]),
		.ic_tag_addr_o(shadow_outputs_d[ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))-:((ibex_pkg_IC_INDEX_W + (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))) >= (TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))) ? ((ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))) - (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))))) + 1 : ((TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))) - (ibex_pkg_IC_INDEX_W + (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))))) + 1)]),
		.ic_tag_wdata_o(shadow_outputs_d[TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))-:((TagSizeECC + (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))) >= (3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))) ? ((TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))) - (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))))) + 1 : ((ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))) - (TagSizeECC + (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))))) + 1)]),
		.ic_tag_rdata_i(shadow_tag_rdata_q[0]),
		.ic_data_req_o(shadow_outputs_d[ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))-:((3 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))) >= (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))) ? ((ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)))) - (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167)))) + 1 : ((1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 167))) - (ibex_pkg_IC_NUM_WAYS + (1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))))) + 1)]),
		.ic_data_write_o(shadow_outputs_d[1 + (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))]),
		.ic_data_addr_o(shadow_outputs_d[ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)-:((ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)) >= (LineSizeECC + 167) ? ((ibex_pkg_IC_INDEX_W + (LineSizeECC + 166)) - (LineSizeECC + 167)) + 1 : ((LineSizeECC + 167) - (ibex_pkg_IC_INDEX_W + (LineSizeECC + 166))) + 1)]),
		.ic_data_wdata_o(shadow_outputs_d[LineSizeECC + 166-:((LineSizeECC + 166) >= 167 ? LineSizeECC + 0 : 168 - (LineSizeECC + 166))]),
		.ic_data_rdata_i(shadow_data_rdata_q[0]),
		.ic_scr_key_valid_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24)]),
		.ic_scr_key_req_o(shadow_outputs_d[166]),
		.irq_software_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 24 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 0)]),
		.irq_timer_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 23 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 1)]),
		.irq_external_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 22 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 2)]),
		.irq_fast_i(shadow_inputs_q[((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 21 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 3) : (0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 21 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 3)) + 14)-:15]),
		.irq_nm_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 6 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 18)]),
		.irq_pending_o(shadow_outputs_d[165]),
		.debug_req_i(shadow_inputs_q[0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 5 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 19)]),
		.crash_dump_o(shadow_outputs_d[164-:160]),
		.double_fault_seen_o(shadow_outputs_d[4]),
		.fetch_enable_i(shadow_inputs_q[((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 4 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 20) : (0 + ((((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 24) >= 0 ? 4 : ((((((2 + MemDataWidth) + 3) + MemDataWidth) + 1) + RegFileDataWidth) + RegFileDataWidth) + 20)) + 3)-:4]),
		.alert_minor_o(shadow_alert_minor),
		.alert_major_internal_o(shadow_alert_major_internal),
		.alert_major_bus_o(shadow_alert_major_bus),
		.core_busy_o(shadow_outputs_d[3-:4])
	);
	always @(posedge clk_i) shadow_outputs_q <= shadow_outputs_d;
	wire outputs_mismatch;
	assign outputs_mismatch = enable_cmp_q & (shadow_outputs_q != core_outputs_q[(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? 0 : (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) + 0+:(((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + 3) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + 3) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166) >= 0 ? (((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 167 : 1 - ((((((((((((71 + MemDataWidth) + 18) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 166))]);
	assign alert_major_internal_o = outputs_mismatch | shadow_alert_major_internal;
	assign alert_major_bus_o = shadow_alert_major_bus;
	assign alert_minor_o = shadow_alert_minor;
endmodule
module ibex_multdiv_fast (
	clk_i,
	rst_ni,
	mult_en_i,
	div_en_i,
	mult_sel_i,
	div_sel_i,
	operator_i,
	signed_mode_i,
	op_a_i,
	op_b_i,
	alu_adder_ext_i,
	alu_adder_i,
	equal_to_zero_i,
	data_ind_timing_i,
	alu_operand_a_o,
	alu_operand_b_o,
	imd_val_q_i,
	imd_val_d_o,
	imd_val_we_o,
	multdiv_ready_id_i,
	multdiv_result_o,
	valid_o
);
	parameter integer RV32M = 32'sd2;
	input wire clk_i;
	input wire rst_ni;
	input wire mult_en_i;
	input wire div_en_i;
	input wire mult_sel_i;
	input wire div_sel_i;
	input wire [1:0] operator_i;
	input wire [1:0] signed_mode_i;
	input wire [31:0] op_a_i;
	input wire [31:0] op_b_i;
	input wire [33:0] alu_adder_ext_i;
	input wire [31:0] alu_adder_i;
	input wire equal_to_zero_i;
	input wire data_ind_timing_i;
	output reg [32:0] alu_operand_a_o;
	output reg [32:0] alu_operand_b_o;
	input wire [67:0] imd_val_q_i;
	output wire [67:0] imd_val_d_o;
	output wire [1:0] imd_val_we_o;
	input wire multdiv_ready_id_i;
	output wire [31:0] multdiv_result_o;
	output wire valid_o;
	wire signed [34:0] mac_res_signed;
	wire [34:0] mac_res_ext;
	wire [33:0] accum;
	wire sign_a;
	wire sign_b;
	reg mult_valid;
	wire signed_mult;
	reg [33:0] mac_res_d;
	reg [33:0] op_remainder_d;
	wire [33:0] mac_res;
	wire div_sign_a;
	wire div_sign_b;
	reg is_greater_equal;
	wire div_change_sign;
	wire rem_change_sign;
	wire [31:0] one_shift;
	wire [31:0] op_denominator_q;
	reg [31:0] op_numerator_q;
	reg [31:0] op_quotient_q;
	reg [31:0] op_denominator_d;
	reg [31:0] op_numerator_d;
	reg [31:0] op_quotient_d;
	wire [31:0] next_remainder;
	wire [32:0] next_quotient;
	wire [31:0] res_adder_h;
	reg div_valid;
	reg [4:0] div_counter_q;
	reg [4:0] div_counter_d;
	wire multdiv_en;
	reg mult_hold;
	reg div_hold;
	reg div_by_zero_d;
	reg div_by_zero_q;
	wire mult_en_internal;
	wire div_en_internal;
	reg [2:0] md_state_q;
	reg [2:0] md_state_d;
	wire unused_mult_sel_i;
	assign unused_mult_sel_i = mult_sel_i;
	assign mult_en_internal = mult_en_i & ~mult_hold;
	assign div_en_internal = div_en_i & ~div_hold;
	always @(posedge clk_i)
		if (!rst_ni) begin
			div_counter_q <= 1'sb0;
			md_state_q <= 3'd0;
			op_numerator_q <= 1'sb0;
			op_quotient_q <= 1'sb0;
			div_by_zero_q <= 1'sb0;
		end
		else if (div_en_internal) begin
			div_counter_q <= div_counter_d;
			op_numerator_q <= op_numerator_d;
			op_quotient_q <= op_quotient_d;
			md_state_q <= md_state_d;
			div_by_zero_q <= div_by_zero_d;
		end
	assign multdiv_en = mult_en_internal | div_en_internal;
	assign imd_val_d_o[34+:34] = (div_sel_i ? op_remainder_d : mac_res_d);
	assign imd_val_we_o[0] = multdiv_en;
	assign imd_val_d_o[0+:34] = {2'b00, op_denominator_d};
	assign imd_val_we_o[1] = div_en_internal;
	assign op_denominator_q = imd_val_q_i[31-:32];
	wire [1:0] unused_imd_val;
	assign unused_imd_val = imd_val_q_i[33-:2];
	wire unused_mac_res_ext;
	assign unused_mac_res_ext = mac_res_ext[34];
	assign signed_mult = signed_mode_i != 2'b00;
	assign multdiv_result_o = (div_sel_i ? imd_val_q_i[65-:32] : mac_res_d[31:0]);
	generate
		if (1) begin : gen_multi_auto_synth
			reg [32:0] operand_a_r;
			reg [32:0] operand_b_r;
			reg [31:0] mult_result_low;
			reg [63:0] mult_result_full;
			reg [31:0] mult_result;
			always @(*) begin
				if (signed_mult) begin
					operand_a_r = {op_a_i[31], op_a_i[31:0]};
					operand_b_r = {op_b_i[31], op_b_i[31:0]};
				end
				else begin
					operand_a_r = {1'b0, op_a_i[31:0]};
					operand_b_r = {1'b0, op_b_i[31:0]};
				end
				mult_result_low = op_a_i * op_b_i;
				mult_result_full = {{31 {operand_a_r[32]}}, operand_a_r} * {{31 {operand_b_r[32]}}, operand_b_r};
				mult_result = (operator_i == 2'd0 ? mult_result_low : mult_result_full[63:32]);
				mac_res_d = {2'b00, mult_result};
				mult_valid = mult_en_i;
				mult_hold = 1'b0;
			end
		end
	endgenerate
	assign res_adder_h = alu_adder_ext_i[32:1];
	wire [1:0] unused_alu_adder_ext;
	assign unused_alu_adder_ext = {alu_adder_ext_i[33], alu_adder_ext_i[0]};
	assign next_remainder = (is_greater_equal ? res_adder_h[31:0] : imd_val_q_i[65-:32]);
	assign next_quotient = (is_greater_equal ? {1'b0, op_quotient_q} | {1'b0, one_shift} : {1'b0, op_quotient_q});
	assign one_shift = 32'b00000000000000000000000000000001 << div_counter_q;
	always @(*)
		if ((imd_val_q_i[65] ^ op_denominator_q[31]) == 1'b0)
			is_greater_equal = res_adder_h[31] == 1'b0;
		else
			is_greater_equal = imd_val_q_i[65];
	assign div_sign_a = op_a_i[31] & signed_mode_i[0];
	assign div_sign_b = op_b_i[31] & signed_mode_i[1];
	assign div_change_sign = (div_sign_a ^ div_sign_b) & ~div_by_zero_q;
	assign rem_change_sign = div_sign_a;
	always @(*) begin
		div_counter_d = div_counter_q - 5'h01;
		op_remainder_d = imd_val_q_i[34+:34];
		op_quotient_d = op_quotient_q;
		md_state_d = md_state_q;
		op_numerator_d = op_numerator_q;
		op_denominator_d = op_denominator_q;
		alu_operand_a_o = 33'h000000001;
		alu_operand_b_o = {~op_b_i, 1'b1};
		div_valid = 1'b0;
		div_hold = 1'b0;
		div_by_zero_d = div_by_zero_q;
		case (md_state_q)
			3'd0: begin
				if (operator_i == 2'd2) begin
					op_remainder_d = 1'sb1;
					md_state_d = (!data_ind_timing_i && equal_to_zero_i ? 3'd6 : 3'd1);
					div_by_zero_d = equal_to_zero_i;
				end
				else begin
					op_remainder_d = {2'b00, op_a_i};
					md_state_d = (!data_ind_timing_i && equal_to_zero_i ? 3'd6 : 3'd1);
				end
				alu_operand_a_o = 33'h000000001;
				alu_operand_b_o = {~op_b_i, 1'b1};
				div_counter_d = 5'd31;
			end
			3'd1: begin
				op_quotient_d = 1'sb0;
				op_numerator_d = (div_sign_a ? alu_adder_i : op_a_i);
				md_state_d = 3'd2;
				div_counter_d = 5'd31;
				alu_operand_a_o = 33'h000000001;
				alu_operand_b_o = {~op_a_i, 1'b1};
			end
			3'd2: begin
				op_remainder_d = {33'h000000000, op_numerator_q[31]};
				op_denominator_d = (div_sign_b ? alu_adder_i : op_b_i);
				md_state_d = 3'd3;
				div_counter_d = 5'd31;
				alu_operand_a_o = 33'h000000001;
				alu_operand_b_o = {~op_b_i, 1'b1};
			end
			3'd3: begin
				op_remainder_d = {1'b0, next_remainder[31:0], op_numerator_q[div_counter_d]};
				op_quotient_d = next_quotient[31:0];
				md_state_d = (div_counter_q == 5'd1 ? 3'd4 : 3'd3);
				alu_operand_a_o = {imd_val_q_i[65-:32], 1'b1};
				alu_operand_b_o = {~op_denominator_q[31:0], 1'b1};
			end
			3'd4: begin
				if (operator_i == 2'd2)
					op_remainder_d = {1'b0, next_quotient};
				else
					op_remainder_d = {2'b00, next_remainder[31:0]};
				alu_operand_a_o = {imd_val_q_i[65-:32], 1'b1};
				alu_operand_b_o = {~op_denominator_q[31:0], 1'b1};
				md_state_d = 3'd5;
			end
			3'd5: begin
				md_state_d = 3'd6;
				if (operator_i == 2'd2)
					op_remainder_d = (div_change_sign ? {2'h0, alu_adder_i} : imd_val_q_i[34+:34]);
				else
					op_remainder_d = (rem_change_sign ? {2'h0, alu_adder_i} : imd_val_q_i[34+:34]);
				alu_operand_a_o = 33'h000000001;
				alu_operand_b_o = {~imd_val_q_i[65-:32], 1'b1};
			end
			3'd6: begin
				md_state_d = 3'd0;
				div_hold = ~multdiv_ready_id_i;
				div_valid = 1'b1;
			end
			default: md_state_d = 3'd0;
		endcase
	end
	assign valid_o = mult_valid | div_valid;
endmodule
module ibex_ex_block (
	clk_i,
	rst_ni,
	alu_operator_i,
	alu_operand_a_i,
	alu_operand_b_i,
	alu_instr_first_cycle_i,
	bt_a_operand_i,
	bt_b_operand_i,
	multdiv_operator_i,
	mult_en_i,
	div_en_i,
	mult_sel_i,
	div_sel_i,
	multdiv_signed_mode_i,
	multdiv_operand_a_i,
	multdiv_operand_b_i,
	multdiv_ready_id_i,
	data_ind_timing_i,
	imd_val_we_o,
	imd_val_d_o,
	imd_val_q_i,
	alu_adder_result_ex_o,
	result_ex_o,
	branch_target_o,
	branch_decision_o,
	ex_valid_o
);
	parameter integer RV32M = 32'sd2;
	parameter integer RV32B = 32'sd0;
	parameter [0:0] BranchTargetALU = 0;
	input wire clk_i;
	input wire rst_ni;
	input wire [6:0] alu_operator_i;
	input wire [31:0] alu_operand_a_i;
	input wire [31:0] alu_operand_b_i;
	input wire alu_instr_first_cycle_i;
	input wire [31:0] bt_a_operand_i;
	input wire [31:0] bt_b_operand_i;
	input wire [1:0] multdiv_operator_i;
	input wire mult_en_i;
	input wire div_en_i;
	input wire mult_sel_i;
	input wire div_sel_i;
	input wire [1:0] multdiv_signed_mode_i;
	input wire [31:0] multdiv_operand_a_i;
	input wire [31:0] multdiv_operand_b_i;
	input wire multdiv_ready_id_i;
	input wire data_ind_timing_i;
	output wire [1:0] imd_val_we_o;
	output wire [67:0] imd_val_d_o;
	input wire [67:0] imd_val_q_i;
	output wire [31:0] alu_adder_result_ex_o;
	output wire [31:0] result_ex_o;
	output wire [31:0] branch_target_o;
	output wire branch_decision_o;
	output wire ex_valid_o;
	wire [31:0] alu_result;
	wire [31:0] multdiv_result;
	wire [32:0] multdiv_alu_operand_b;
	wire [32:0] multdiv_alu_operand_a;
	wire [33:0] alu_adder_result_ext;
	wire alu_cmp_result;
	wire alu_is_equal_result;
	wire multdiv_valid;
	wire multdiv_sel;
	wire [63:0] alu_imd_val_q;
	wire [63:0] alu_imd_val_d;
	wire [1:0] alu_imd_val_we;
	wire [67:0] multdiv_imd_val_d;
	wire [1:0] multdiv_imd_val_we;
	generate
		if (RV32M != 32'sd0) begin : gen_multdiv_m
			assign multdiv_sel = mult_sel_i | div_sel_i;
		end
		else begin : gen_multdiv_no_m
			assign multdiv_sel = 1'b0;
		end
	endgenerate
	assign imd_val_d_o[34+:34] = (multdiv_sel ? multdiv_imd_val_d[34+:34] : {2'b00, alu_imd_val_d[32+:32]});
	assign imd_val_d_o[0+:34] = (multdiv_sel ? multdiv_imd_val_d[0+:34] : {2'b00, alu_imd_val_d[0+:32]});
	assign imd_val_we_o = (multdiv_sel ? multdiv_imd_val_we : alu_imd_val_we);
	assign alu_imd_val_q = {imd_val_q_i[65-:32], imd_val_q_i[31-:32]};
	assign result_ex_o = (multdiv_sel ? multdiv_result : alu_result);
	assign branch_decision_o = alu_cmp_result;
	generate
		if (BranchTargetALU) begin : g_branch_target_alu
			wire [32:0] bt_alu_result;
			wire unused_bt_carry;
			assign bt_alu_result = bt_a_operand_i + bt_b_operand_i;
			assign unused_bt_carry = bt_alu_result[32];
			assign branch_target_o = bt_alu_result[31:0];
		end
		else begin : g_no_branch_target_alu
			wire [31:0] unused_bt_a_operand;
			wire [31:0] unused_bt_b_operand;
			assign unused_bt_a_operand = bt_a_operand_i;
			assign unused_bt_b_operand = bt_b_operand_i;
			assign branch_target_o = alu_adder_result_ex_o;
		end
	endgenerate
	ibex_alu #(.RV32B(RV32B)) alu_i(
		.operator_i(alu_operator_i),
		.operand_a_i(alu_operand_a_i),
		.operand_b_i(alu_operand_b_i),
		.instr_first_cycle_i(alu_instr_first_cycle_i),
		.imd_val_q_i(alu_imd_val_q),
		.imd_val_we_o(alu_imd_val_we),
		.imd_val_d_o(alu_imd_val_d),
		.multdiv_operand_a_i(multdiv_alu_operand_a),
		.multdiv_operand_b_i(multdiv_alu_operand_b),
		.multdiv_sel_i(multdiv_sel),
		.adder_result_o(alu_adder_result_ex_o),
		.adder_result_ext_o(alu_adder_result_ext),
		.result_o(alu_result),
		.comparison_result_o(alu_cmp_result),
		.is_equal_result_o(alu_is_equal_result)
	);
	generate
		if (RV32M == 32'sd1) begin : gen_multdiv_slow
			ibex_multdiv_slow multdiv_i(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.mult_en_i(mult_en_i),
				.div_en_i(div_en_i),
				.mult_sel_i(mult_sel_i),
				.div_sel_i(div_sel_i),
				.operator_i(multdiv_operator_i),
				.signed_mode_i(multdiv_signed_mode_i),
				.op_a_i(multdiv_operand_a_i),
				.op_b_i(multdiv_operand_b_i),
				.alu_adder_ext_i(alu_adder_result_ext),
				.alu_adder_i(alu_adder_result_ex_o),
				.equal_to_zero_i(alu_is_equal_result),
				.data_ind_timing_i(data_ind_timing_i),
				.valid_o(multdiv_valid),
				.alu_operand_a_o(multdiv_alu_operand_a),
				.alu_operand_b_o(multdiv_alu_operand_b),
				.imd_val_q_i(imd_val_q_i),
				.imd_val_d_o(multdiv_imd_val_d),
				.imd_val_we_o(multdiv_imd_val_we),
				.multdiv_ready_id_i(multdiv_ready_id_i),
				.multdiv_result_o(multdiv_result)
			);
		end
		else if ((RV32M == 32'sd2) || (RV32M == 32'sd3)) begin : gen_multdiv_fast
			ibex_multdiv_fast #(.RV32M(RV32M)) multdiv_i(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.mult_en_i(mult_en_i),
				.div_en_i(div_en_i),
				.mult_sel_i(mult_sel_i),
				.div_sel_i(div_sel_i),
				.operator_i(multdiv_operator_i),
				.signed_mode_i(multdiv_signed_mode_i),
				.op_a_i(multdiv_operand_a_i),
				.op_b_i(multdiv_operand_b_i),
				.alu_operand_a_o(multdiv_alu_operand_a),
				.alu_operand_b_o(multdiv_alu_operand_b),
				.alu_adder_ext_i(alu_adder_result_ext),
				.alu_adder_i(alu_adder_result_ex_o),
				.equal_to_zero_i(alu_is_equal_result),
				.data_ind_timing_i(data_ind_timing_i),
				.imd_val_q_i(imd_val_q_i),
				.imd_val_d_o(multdiv_imd_val_d),
				.imd_val_we_o(multdiv_imd_val_we),
				.multdiv_ready_id_i(multdiv_ready_id_i),
				.valid_o(multdiv_valid),
				.multdiv_result_o(multdiv_result)
			);
		end
	endgenerate
	assign ex_valid_o = (multdiv_sel ? multdiv_valid : ~(|alu_imd_val_we));
endmodule
module ibex_branch_predict (
	clk_i,
	rst_ni,
	fetch_rdata_i,
	fetch_pc_i,
	fetch_valid_i,
	predict_branch_taken_o,
	predict_branch_pc_o
);
	input wire clk_i;
	input wire rst_ni;
	input wire [31:0] fetch_rdata_i;
	input wire [31:0] fetch_pc_i;
	input wire fetch_valid_i;
	output wire predict_branch_taken_o;
	output wire [31:0] predict_branch_pc_o;
	wire [31:0] imm_j_type;
	wire [31:0] imm_b_type;
	wire [31:0] imm_cj_type;
	wire [31:0] imm_cb_type;
	reg [31:0] branch_imm;
	wire [31:0] instr;
	wire instr_j;
	wire instr_b;
	wire instr_cj;
	wire instr_cb;
	wire instr_b_taken;
	assign instr = fetch_rdata_i;
	assign imm_j_type = {{12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
	assign imm_b_type = {{19 {instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
	assign imm_cj_type = {{20 {instr[12]}}, instr[12], instr[8], instr[10:9], instr[6], instr[7], instr[2], instr[11], instr[5:3], 1'b0};
	assign imm_cb_type = {{23 {instr[12]}}, instr[12], instr[6:5], instr[2], instr[11:10], instr[4:3], 1'b0};
	assign instr_b = instr[6:0] == 7'h63;
	assign instr_j = instr[6:0] == 7'h6f;
	assign instr_cb = (instr[1:0] == 2'b01) & ((instr[15:13] == 3'b110) | (instr[15:13] == 3'b111));
	assign instr_cj = (instr[1:0] == 2'b01) & ((instr[15:13] == 3'b101) | (instr[15:13] == 3'b001));
	always @(*) begin
		branch_imm = imm_b_type;
		case (1'b1)
			instr_j: branch_imm = imm_j_type;
			instr_b: branch_imm = imm_b_type;
			instr_cj: branch_imm = imm_cj_type;
			instr_cb: branch_imm = imm_cb_type;
			default:
				;
		endcase
	end
	assign instr_b_taken = (instr_b & imm_b_type[31]) | (instr_cb & imm_cb_type[31]);
	assign predict_branch_taken_o = fetch_valid_i & ((instr_j | instr_cj) | instr_b_taken);
	assign predict_branch_pc_o = fetch_pc_i + branch_imm;
endmodule
module ibex_register_file_ff (
	clk_i,
	rst_ni,
	test_en_i,
	dummy_instr_id_i,
	dummy_instr_wb_i,
	raddr_a_i,
	rdata_a_o,
	raddr_b_i,
	rdata_b_o,
	waddr_a_i,
	wdata_a_i,
	we_a_i,
	err_o
);
	parameter [0:0] RV32E = 0;
	parameter [31:0] DataWidth = 32;
	parameter [0:0] DummyInstructions = 0;
	parameter [0:0] WrenCheck = 0;
	parameter [DataWidth - 1:0] WordZeroVal = 1'sb0;
	input wire clk_i;
	input wire rst_ni;
	input wire test_en_i;
	input wire dummy_instr_id_i;
	input wire dummy_instr_wb_i;
	input wire [4:0] raddr_a_i;
	output wire [DataWidth - 1:0] rdata_a_o;
	input wire [4:0] raddr_b_i;
	output wire [DataWidth - 1:0] rdata_b_o;
	input wire [4:0] waddr_a_i;
	input wire [DataWidth - 1:0] wdata_a_i;
	input wire we_a_i;
	output wire err_o;
	localparam [31:0] ADDR_WIDTH = (RV32E ? 4 : 5);
	localparam [31:0] NUM_WORDS = 2 ** ADDR_WIDTH;
	wire [DataWidth - 1:0] rf_reg [0:NUM_WORDS - 1];
	reg [NUM_WORDS - 1:0] we_a_dec;
	function automatic [4:0] sv2v_cast_5;
		input reg [4:0] inp;
		sv2v_cast_5 = inp;
	endfunction
	always @(*) begin : we_a_decoder
		begin : sv2v_autoblock_1
			reg [31:0] i;
			for (i = 0; i < NUM_WORDS; i = i + 1)
				we_a_dec[i] = (waddr_a_i == sv2v_cast_5(i) ? we_a_i : 1'b0);
		end
	end
	generate
		if (WrenCheck) begin : gen_wren_check
			wire [NUM_WORDS - 1:0] we_a_dec_buf;
			prim_buf #(.Width(NUM_WORDS)) u_prim_buf(
				.in_i(we_a_dec),
				.out_o(we_a_dec_buf)
			);
			prim_onehot_check #(
				.AddrWidth(ADDR_WIDTH),
				.AddrCheck(1),
				.EnableCheck(1)
			) u_prim_onehot_check(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.oh_i(we_a_dec_buf),
				.addr_i(waddr_a_i),
				.en_i(we_a_i),
				.err_o(err_o)
			);
		end
		else begin : gen_no_wren_check
			wire unused_strobe;
			assign unused_strobe = we_a_dec[0];
			assign err_o = 1'b0;
		end
	endgenerate
	genvar i;
	generate
		for (i = 1; i < NUM_WORDS; i = i + 1) begin : g_rf_flops
			reg [DataWidth - 1:0] rf_reg_q;
			always @(posedge clk_i)
				if (!rst_ni)
					rf_reg_q <= WordZeroVal;
				else if (we_a_dec[i])
					rf_reg_q <= wdata_a_i;
			assign rf_reg[i] = rf_reg_q;
		end
		if (DummyInstructions) begin : g_dummy_r0
			wire we_r0_dummy;
			reg [DataWidth - 1:0] rf_r0_q;
			assign we_r0_dummy = we_a_i & dummy_instr_wb_i;
			always @(posedge clk_i)
				if (!rst_ni)
					rf_r0_q <= WordZeroVal;
				else if (we_r0_dummy)
					rf_r0_q <= wdata_a_i;
			assign rf_reg[0] = (dummy_instr_id_i ? rf_r0_q : WordZeroVal);
		end
		else begin : g_normal_r0
			wire unused_dummy_instr;
			assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;
			assign rf_reg[0] = WordZeroVal;
		end
	endgenerate
	assign rdata_a_o = rf_reg[raddr_a_i];
	assign rdata_b_o = rf_reg[raddr_b_i];
	wire unused_test_en;
	assign unused_test_en = test_en_i;
endmodule
module ibex_csr (
	clk_i,
	rst_ni,
	wr_data_i,
	wr_en_i,
	rd_data_o,
	rd_error_o
);
	parameter [31:0] Width = 32;
	parameter [0:0] ShadowCopy = 1'b0;
	parameter [Width - 1:0] ResetValue = 1'sb0;
	input wire clk_i;
	input wire rst_ni;
	input wire [Width - 1:0] wr_data_i;
	input wire wr_en_i;
	output wire [Width - 1:0] rd_data_o;
	output wire rd_error_o;
	reg [Width - 1:0] rdata_q;
	always @(posedge clk_i)
		if (!rst_ni)
			rdata_q <= ResetValue;
		else if (wr_en_i)
			rdata_q <= wr_data_i;
	assign rd_data_o = rdata_q;
	generate
		if (ShadowCopy) begin : gen_shadow
			reg [Width - 1:0] shadow_q;
			always @(posedge clk_i)
				if (!rst_ni)
					shadow_q <= ~ResetValue;
				else if (wr_en_i)
					shadow_q <= ~wr_data_i;
			assign rd_error_o = rdata_q != ~shadow_q;
		end
		else begin : gen_no_shadow
			assign rd_error_o = 1'b0;
		end
	endgenerate
endmodule
module ibex_decoder (
	clk_i,
	rst_ni,
	illegal_insn_o,
	ebrk_insn_o,
	mret_insn_o,
	dret_insn_o,
	ecall_insn_o,
	wfi_insn_o,
	jump_set_o,
	branch_taken_i,
	icache_inval_o,
	instr_first_cycle_i,
	instr_rdata_i,
	instr_rdata_alu_i,
	illegal_c_insn_i,
	imm_a_mux_sel_o,
	imm_b_mux_sel_o,
	bt_a_mux_sel_o,
	bt_b_mux_sel_o,
	imm_i_type_o,
	imm_s_type_o,
	imm_b_type_o,
	imm_u_type_o,
	imm_j_type_o,
	zimm_rs1_type_o,
	rf_wdata_sel_o,
	rf_we_o,
	rf_raddr_a_o,
	rf_raddr_b_o,
	rf_waddr_o,
	rf_ren_a_o,
	rf_ren_b_o,
	alu_operator_o,
	alu_op_a_mux_sel_o,
	alu_op_b_mux_sel_o,
	alu_multicycle_o,
	mult_en_o,
	div_en_o,
	mult_sel_o,
	div_sel_o,
	multdiv_operator_o,
	multdiv_signed_mode_o,
	csr_access_o,
	csr_op_o,
	data_req_o,
	data_we_o,
	data_type_o,
	data_sign_extension_o,
	jump_in_dec_o,
	branch_in_dec_o
);
	parameter [0:0] RV32E = 0;
	parameter integer RV32M = 32'sd2;
	parameter integer RV32B = 32'sd0;
	parameter [0:0] BranchTargetALU = 0;
	input wire clk_i;
	input wire rst_ni;
	output wire illegal_insn_o;
	output reg ebrk_insn_o;
	output reg mret_insn_o;
	output reg dret_insn_o;
	output reg ecall_insn_o;
	output reg wfi_insn_o;
	output reg jump_set_o;
	input wire branch_taken_i;
	output reg icache_inval_o;
	input wire instr_first_cycle_i;
	input wire [31:0] instr_rdata_i;
	input wire [31:0] instr_rdata_alu_i;
	input wire illegal_c_insn_i;
	output reg imm_a_mux_sel_o;
	output reg [2:0] imm_b_mux_sel_o;
	output reg [1:0] bt_a_mux_sel_o;
	output reg [2:0] bt_b_mux_sel_o;
	output wire [31:0] imm_i_type_o;
	output wire [31:0] imm_s_type_o;
	output wire [31:0] imm_b_type_o;
	output wire [31:0] imm_u_type_o;
	output wire [31:0] imm_j_type_o;
	output wire [31:0] zimm_rs1_type_o;
	output reg rf_wdata_sel_o;
	output wire rf_we_o;
	output wire [4:0] rf_raddr_a_o;
	output wire [4:0] rf_raddr_b_o;
	output wire [4:0] rf_waddr_o;
	output reg rf_ren_a_o;
	output reg rf_ren_b_o;
	output reg [6:0] alu_operator_o;
	output reg [1:0] alu_op_a_mux_sel_o;
	output reg alu_op_b_mux_sel_o;
	output reg alu_multicycle_o;
	output wire mult_en_o;
	output wire div_en_o;
	output reg mult_sel_o;
	output reg div_sel_o;
	output reg [1:0] multdiv_operator_o;
	output reg [1:0] multdiv_signed_mode_o;
	output reg csr_access_o;
	output reg [1:0] csr_op_o;
	output reg data_req_o;
	output reg data_we_o;
	output reg [1:0] data_type_o;
	output reg data_sign_extension_o;
	output reg jump_in_dec_o;
	output reg branch_in_dec_o;
	reg illegal_insn;
	wire illegal_reg_rv32e;
	reg csr_illegal;
	reg rf_we;
	wire [31:0] instr;
	wire [31:0] instr_alu;
	wire [9:0] unused_instr_alu;
	wire [4:0] instr_rs1;
	wire [4:0] instr_rs2;
	wire [4:0] instr_rs3;
	wire [4:0] instr_rd;
	reg use_rs3_d;
	reg use_rs3_q;
	reg [1:0] csr_op;
	reg [6:0] opcode;
	reg [6:0] opcode_alu;
	assign instr = instr_rdata_i;
	assign instr_alu = instr_rdata_alu_i;
	assign imm_i_type_o = {{20 {instr[31]}}, instr[31:20]};
	assign imm_s_type_o = {{20 {instr[31]}}, instr[31:25], instr[11:7]};
	assign imm_b_type_o = {{19 {instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
	assign imm_u_type_o = {instr[31:12], 12'b000000000000};
	assign imm_j_type_o = {{12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
	assign zimm_rs1_type_o = {27'b000000000000000000000000000, instr_rs1};
	generate
		if (RV32B != 32'sd0) begin : gen_rs3_flop
			always @(posedge clk_i)
				if (!rst_ni)
					use_rs3_q <= 1'b0;
				else
					use_rs3_q <= use_rs3_d;
		end
		else begin : gen_no_rs3_flop
			wire unused_clk;
			wire unused_rst_n;
			assign unused_clk = clk_i;
			assign unused_rst_n = rst_ni;
			wire [1:1] sv2v_tmp_44B6F;
			assign sv2v_tmp_44B6F = use_rs3_d;
			always @(*) use_rs3_q = sv2v_tmp_44B6F;
		end
	endgenerate
	assign instr_rs1 = instr[19:15];
	assign instr_rs2 = instr[24:20];
	assign instr_rs3 = instr[31:27];
	assign rf_raddr_a_o = (use_rs3_q & ~instr_first_cycle_i ? instr_rs3 : instr_rs1);
	assign rf_raddr_b_o = instr_rs2;
	assign instr_rd = instr[11:7];
	assign rf_waddr_o = instr_rd;
	generate
		if (RV32E) begin : gen_rv32e_reg_check_active
			assign illegal_reg_rv32e = ((rf_raddr_a_o[4] & (alu_op_a_mux_sel_o == 2'd0)) | (rf_raddr_b_o[4] & (alu_op_b_mux_sel_o == 1'd0))) | (rf_waddr_o[4] & rf_we);
		end
		else begin : gen_rv32e_reg_check_inactive
			assign illegal_reg_rv32e = 1'b0;
		end
	endgenerate
	always @(*) begin : csr_operand_check
		csr_op_o = csr_op;
		if (((csr_op == 2'd2) || (csr_op == 2'd3)) && (instr_rs1 == {5 {1'sb0}}))
			csr_op_o = 2'd0;
	end
	always @(*) begin
		jump_in_dec_o = 1'b0;
		jump_set_o = 1'b0;
		branch_in_dec_o = 1'b0;
		icache_inval_o = 1'b0;
		multdiv_operator_o = 2'd0;
		multdiv_signed_mode_o = 2'b00;
		rf_wdata_sel_o = 1'd0;
		rf_we = 1'b0;
		rf_ren_a_o = 1'b0;
		rf_ren_b_o = 1'b0;
		csr_access_o = 1'b0;
		csr_illegal = 1'b0;
		csr_op = 2'd0;
		data_we_o = 1'b0;
		data_type_o = 2'b00;
		data_sign_extension_o = 1'b0;
		data_req_o = 1'b0;
		illegal_insn = 1'b0;
		ebrk_insn_o = 1'b0;
		mret_insn_o = 1'b0;
		dret_insn_o = 1'b0;
		ecall_insn_o = 1'b0;
		wfi_insn_o = 1'b0;
		opcode = instr[6:0];
		case (opcode)
			7'h6f: begin
				jump_in_dec_o = 1'b1;
				if (instr_first_cycle_i) begin
					rf_we = BranchTargetALU;
					jump_set_o = 1'b1;
				end
				else
					rf_we = 1'b1;
			end
			7'h67: begin
				jump_in_dec_o = 1'b1;
				if (instr_first_cycle_i) begin
					rf_we = BranchTargetALU;
					jump_set_o = 1'b1;
				end
				else
					rf_we = 1'b1;
				if (instr[14:12] != 3'b000)
					illegal_insn = 1'b1;
				rf_ren_a_o = 1'b1;
			end
			7'h63: begin
				branch_in_dec_o = 1'b1;
				case (instr[14:12])
					3'b000, 3'b001, 3'b100, 3'b101, 3'b110, 3'b111: illegal_insn = 1'b0;
					default: illegal_insn = 1'b1;
				endcase
				rf_ren_a_o = 1'b1;
				rf_ren_b_o = 1'b1;
			end
			7'h23: begin
				rf_ren_a_o = 1'b1;
				rf_ren_b_o = 1'b1;
				data_req_o = 1'b1;
				data_we_o = 1'b1;
				if (instr[14])
					illegal_insn = 1'b1;
				case (instr[13:12])
					2'b00: data_type_o = 2'b10;
					2'b01: data_type_o = 2'b01;
					2'b10: data_type_o = 2'b00;
					default: illegal_insn = 1'b1;
				endcase
			end
			7'h03: begin
				rf_ren_a_o = 1'b1;
				data_req_o = 1'b1;
				data_type_o = 2'b00;
				data_sign_extension_o = ~instr[14];
				case (instr[13:12])
					2'b00: data_type_o = 2'b10;
					2'b01: data_type_o = 2'b01;
					2'b10: begin
						data_type_o = 2'b00;
						if (instr[14])
							illegal_insn = 1'b1;
					end
					default: illegal_insn = 1'b1;
				endcase
			end
			7'h37: rf_we = 1'b1;
			7'h17: rf_we = 1'b1;
			7'h13: begin
				rf_ren_a_o = 1'b1;
				rf_we = 1'b1;
				case (instr[14:12])
					3'b000, 3'b010, 3'b011, 3'b100, 3'b110, 3'b111: illegal_insn = 1'b0;
					3'b001:
						case (instr[31:27])
							5'b00000: illegal_insn = (instr[26:25] == 2'b00 ? 1'b0 : 1'b1);
							5'b00100: illegal_insn = ((RV32B == 32'sd2) || (RV32B == 32'sd3) ? 1'b0 : 1'b1);
							5'b01001, 5'b00101, 5'b01101: illegal_insn = (RV32B != 32'sd0 ? 1'b0 : 1'b1);
							5'b00001:
								if (instr[26] == 1'b0)
									illegal_insn = ((RV32B == 32'sd2) || (RV32B == 32'sd3) ? 1'b0 : 1'b1);
								else
									illegal_insn = 1'b1;
							5'b01100:
								case (instr[26:20])
									7'b0000000, 7'b0000001, 7'b0000010, 7'b0000100, 7'b0000101: illegal_insn = (RV32B != 32'sd0 ? 1'b0 : 1'b1);
									7'b0010000, 7'b0010001, 7'b0010010, 7'b0011000, 7'b0011001, 7'b0011010: illegal_insn = ((RV32B == 32'sd2) || (RV32B == 32'sd3) ? 1'b0 : 1'b1);
									default: illegal_insn = 1'b1;
								endcase
							default: illegal_insn = 1'b1;
						endcase
					3'b101:
						if (instr[26])
							illegal_insn = (RV32B != 32'sd0 ? 1'b0 : 1'b1);
						else
							case (instr[31:27])
								5'b00000, 5'b01000: illegal_insn = (instr[26:25] == 2'b00 ? 1'b0 : 1'b1);
								5'b00100: illegal_insn = ((RV32B == 32'sd2) || (RV32B == 32'sd3) ? 1'b0 : 1'b1);
								5'b01100, 5'b01001: illegal_insn = (RV32B != 32'sd0 ? 1'b0 : 1'b1);
								5'b01101:
									if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
										illegal_insn = 1'b0;
									else if (RV32B == 32'sd1)
										illegal_insn = (instr[24:20] == 5'b11000 ? 1'b0 : 1'b1);
									else
										illegal_insn = 1'b1;
								5'b00101:
									if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
										illegal_insn = 1'b0;
									else if (instr[24:20] == 5'b00111)
										illegal_insn = (RV32B == 32'sd1 ? 1'b0 : 1'b1);
									else
										illegal_insn = 1'b1;
								5'b00001:
									if (instr[26] == 1'b0)
										illegal_insn = ((RV32B == 32'sd2) || (RV32B == 32'sd3) ? 1'b0 : 1'b1);
									else
										illegal_insn = 1'b1;
								default: illegal_insn = 1'b1;
							endcase
					default: illegal_insn = 1'b1;
				endcase
			end
			7'h33: begin
				rf_ren_a_o = 1'b1;
				rf_ren_b_o = 1'b1;
				rf_we = 1'b1;
				if ({instr[26], instr[13:12]} == 3'b101)
					illegal_insn = (RV32B != 32'sd0 ? 1'b0 : 1'b1);
				else
					case ({instr[31:25], instr[14:12]})
						10'b0000000000, 10'b0100000000, 10'b0000000010, 10'b0000000011, 10'b0000000100, 10'b0000000110, 10'b0000000111, 10'b0000000001, 10'b0000000101, 10'b0100000101: illegal_insn = 1'b0;
						10'b0010000010, 10'b0010000100, 10'b0010000110, 10'b0100000111, 10'b0100000110, 10'b0100000100, 10'b0110000001, 10'b0110000101, 10'b0000101100, 10'b0000101110, 10'b0000101101, 10'b0000101111, 10'b0000100100, 10'b0100100100, 10'b0000100111, 10'b0100100001, 10'b0010100001, 10'b0110100001, 10'b0100100101, 10'b0100100111: illegal_insn = (RV32B != 32'sd0 ? 1'b0 : 1'b1);
						10'b0110100101, 10'b0010100101, 10'b0000100001, 10'b0000100101, 10'b0010100010, 10'b0010100100, 10'b0010100110, 10'b0010000001, 10'b0010000101, 10'b0000101001, 10'b0000101010, 10'b0000101011: illegal_insn = ((RV32B == 32'sd2) || (RV32B == 32'sd3) ? 1'b0 : 1'b1);
						10'b0100100110, 10'b0000100110: illegal_insn = (RV32B == 32'sd3 ? 1'b0 : 1'b1);
						10'b0000001000: begin
							multdiv_operator_o = 2'd0;
							multdiv_signed_mode_o = 2'b00;
							illegal_insn = (RV32M == 32'sd0 ? 1'b1 : 1'b0);
						end
						10'b0000001001: begin
							multdiv_operator_o = 2'd1;
							multdiv_signed_mode_o = 2'b11;
							illegal_insn = (RV32M == 32'sd0 ? 1'b1 : 1'b0);
						end
						10'b0000001010: begin
							multdiv_operator_o = 2'd1;
							multdiv_signed_mode_o = 2'b01;
							illegal_insn = (RV32M == 32'sd0 ? 1'b1 : 1'b0);
						end
						10'b0000001011: begin
							multdiv_operator_o = 2'd1;
							multdiv_signed_mode_o = 2'b00;
							illegal_insn = (RV32M == 32'sd0 ? 1'b1 : 1'b0);
						end
						10'b0000001100: begin
							multdiv_operator_o = 2'd2;
							multdiv_signed_mode_o = 2'b11;
							illegal_insn = (RV32M == 32'sd0 ? 1'b1 : 1'b0);
						end
						10'b0000001101: begin
							multdiv_operator_o = 2'd2;
							multdiv_signed_mode_o = 2'b00;
							illegal_insn = (RV32M == 32'sd0 ? 1'b1 : 1'b0);
						end
						10'b0000001110: begin
							multdiv_operator_o = 2'd3;
							multdiv_signed_mode_o = 2'b11;
							illegal_insn = (RV32M == 32'sd0 ? 1'b1 : 1'b0);
						end
						10'b0000001111: begin
							multdiv_operator_o = 2'd3;
							multdiv_signed_mode_o = 2'b00;
							illegal_insn = (RV32M == 32'sd0 ? 1'b1 : 1'b0);
						end
						default: illegal_insn = 1'b1;
					endcase
			end
			7'h0f:
				case (instr[14:12])
					3'b000: rf_we = 1'b0;
					3'b001: begin
						jump_in_dec_o = 1'b1;
						rf_we = 1'b0;
						if (instr_first_cycle_i) begin
							jump_set_o = 1'b1;
							icache_inval_o = 1'b1;
						end
					end
					default: illegal_insn = 1'b1;
				endcase
			7'h73:
				if (instr[14:12] == 3'b000) begin
					case (instr[31:20])
						12'h000: ecall_insn_o = 1'b1;
						12'h001: ebrk_insn_o = 1'b1;
						12'h302: mret_insn_o = 1'b1;
						12'h7b2: dret_insn_o = 1'b1;
						12'h105: wfi_insn_o = 1'b1;
						default: illegal_insn = 1'b1;
					endcase
					if ((instr_rs1 != 5'b00000) || (instr_rd != 5'b00000))
						illegal_insn = 1'b1;
				end
				else begin
					csr_access_o = 1'b1;
					rf_wdata_sel_o = 1'd1;
					rf_we = 1'b1;
					if (~instr[14])
						rf_ren_a_o = 1'b1;
					case (instr[13:12])
						2'b01: csr_op = 2'd1;
						2'b10: csr_op = 2'd2;
						2'b11: csr_op = 2'd3;
						default: csr_illegal = 1'b1;
					endcase
					illegal_insn = csr_illegal;
				end
			default: illegal_insn = 1'b1;
		endcase
		if (illegal_c_insn_i)
			illegal_insn = 1'b1;
		if (illegal_insn) begin
			rf_we = 1'b0;
			data_req_o = 1'b0;
			data_we_o = 1'b0;
			jump_in_dec_o = 1'b0;
			jump_set_o = 1'b0;
			branch_in_dec_o = 1'b0;
			csr_access_o = 1'b0;
		end
	end
	always @(*) begin
		alu_operator_o = 7'd44;
		alu_op_a_mux_sel_o = 2'd3;
		alu_op_b_mux_sel_o = 1'd1;
		imm_a_mux_sel_o = 1'd1;
		imm_b_mux_sel_o = 3'd0;
		bt_a_mux_sel_o = 2'd2;
		bt_b_mux_sel_o = 3'd0;
		opcode_alu = instr_alu[6:0];
		use_rs3_d = 1'b0;
		alu_multicycle_o = 1'b0;
		mult_sel_o = 1'b0;
		div_sel_o = 1'b0;
		case (opcode_alu)
			7'h6f: begin
				if (BranchTargetALU) begin
					bt_a_mux_sel_o = 2'd2;
					bt_b_mux_sel_o = 3'd4;
				end
				if (instr_first_cycle_i && !BranchTargetALU) begin
					alu_op_a_mux_sel_o = 2'd2;
					alu_op_b_mux_sel_o = 1'd1;
					imm_b_mux_sel_o = 3'd4;
					alu_operator_o = 7'd0;
				end
				else begin
					alu_op_a_mux_sel_o = 2'd2;
					alu_op_b_mux_sel_o = 1'd1;
					imm_b_mux_sel_o = 3'd5;
					alu_operator_o = 7'd0;
				end
			end
			7'h67: begin
				if (BranchTargetALU) begin
					bt_a_mux_sel_o = 2'd0;
					bt_b_mux_sel_o = 3'd0;
				end
				if (instr_first_cycle_i && !BranchTargetALU) begin
					alu_op_a_mux_sel_o = 2'd0;
					alu_op_b_mux_sel_o = 1'd1;
					imm_b_mux_sel_o = 3'd0;
					alu_operator_o = 7'd0;
				end
				else begin
					alu_op_a_mux_sel_o = 2'd2;
					alu_op_b_mux_sel_o = 1'd1;
					imm_b_mux_sel_o = 3'd5;
					alu_operator_o = 7'd0;
				end
			end
			7'h63: begin
				case (instr_alu[14:12])
					3'b000: alu_operator_o = 7'd29;
					3'b001: alu_operator_o = 7'd30;
					3'b100: alu_operator_o = 7'd25;
					3'b101: alu_operator_o = 7'd27;
					3'b110: alu_operator_o = 7'd26;
					3'b111: alu_operator_o = 7'd28;
					default:
						;
				endcase
				if (BranchTargetALU) begin
					bt_a_mux_sel_o = 2'd2;
					bt_b_mux_sel_o = (branch_taken_i ? 3'd2 : 3'd5);
				end
				if (instr_first_cycle_i) begin
					alu_op_a_mux_sel_o = 2'd0;
					alu_op_b_mux_sel_o = 1'd0;
				end
				else if (!BranchTargetALU) begin
					alu_op_a_mux_sel_o = 2'd2;
					alu_op_b_mux_sel_o = 1'd1;
					imm_b_mux_sel_o = (branch_taken_i ? 3'd2 : 3'd5);
					alu_operator_o = 7'd0;
				end
			end
			7'h23: begin
				alu_op_a_mux_sel_o = 2'd0;
				alu_op_b_mux_sel_o = 1'd0;
				alu_operator_o = 7'd0;
				if (!instr_alu[14]) begin
					imm_b_mux_sel_o = 3'd1;
					alu_op_b_mux_sel_o = 1'd1;
				end
			end
			7'h03: begin
				alu_op_a_mux_sel_o = 2'd0;
				alu_operator_o = 7'd0;
				alu_op_b_mux_sel_o = 1'd1;
				imm_b_mux_sel_o = 3'd0;
			end
			7'h37: begin
				alu_op_a_mux_sel_o = 2'd3;
				alu_op_b_mux_sel_o = 1'd1;
				imm_a_mux_sel_o = 1'd1;
				imm_b_mux_sel_o = 3'd3;
				alu_operator_o = 7'd0;
			end
			7'h17: begin
				alu_op_a_mux_sel_o = 2'd2;
				alu_op_b_mux_sel_o = 1'd1;
				imm_b_mux_sel_o = 3'd3;
				alu_operator_o = 7'd0;
			end
			7'h13: begin
				alu_op_a_mux_sel_o = 2'd0;
				alu_op_b_mux_sel_o = 1'd1;
				imm_b_mux_sel_o = 3'd0;
				case (instr_alu[14:12])
					3'b000: alu_operator_o = 7'd0;
					3'b010: alu_operator_o = 7'd43;
					3'b011: alu_operator_o = 7'd44;
					3'b100: alu_operator_o = 7'd2;
					3'b110: alu_operator_o = 7'd3;
					3'b111: alu_operator_o = 7'd4;
					3'b001:
						if (RV32B != 32'sd0)
							case (instr_alu[31:27])
								5'b00000: alu_operator_o = 7'd10;
								5'b00100:
									if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
										alu_operator_o = 7'd12;
								5'b01001: alu_operator_o = 7'd50;
								5'b00101: alu_operator_o = 7'd49;
								5'b01101: alu_operator_o = 7'd51;
								5'b00001:
									if (instr_alu[26] == 0)
										alu_operator_o = 7'd17;
								5'b01100:
									case (instr_alu[26:20])
										7'b0000000: alu_operator_o = 7'd40;
										7'b0000001: alu_operator_o = 7'd41;
										7'b0000010: alu_operator_o = 7'd42;
										7'b0000100: alu_operator_o = 7'd38;
										7'b0000101: alu_operator_o = 7'd39;
										7'b0010000:
											if ((RV32B == 32'sd2) || (RV32B == 32'sd3)) begin
												alu_operator_o = 7'd59;
												alu_multicycle_o = 1'b1;
											end
										7'b0010001:
											if ((RV32B == 32'sd2) || (RV32B == 32'sd3)) begin
												alu_operator_o = 7'd61;
												alu_multicycle_o = 1'b1;
											end
										7'b0010010:
											if ((RV32B == 32'sd2) || (RV32B == 32'sd3)) begin
												alu_operator_o = 7'd63;
												alu_multicycle_o = 1'b1;
											end
										7'b0011000:
											if ((RV32B == 32'sd2) || (RV32B == 32'sd3)) begin
												alu_operator_o = 7'd60;
												alu_multicycle_o = 1'b1;
											end
										7'b0011001:
											if ((RV32B == 32'sd2) || (RV32B == 32'sd3)) begin
												alu_operator_o = 7'd62;
												alu_multicycle_o = 1'b1;
											end
										7'b0011010:
											if ((RV32B == 32'sd2) || (RV32B == 32'sd3)) begin
												alu_operator_o = 7'd64;
												alu_multicycle_o = 1'b1;
											end
										default:
											;
									endcase
								default:
									;
							endcase
						else
							alu_operator_o = 7'd10;
					3'b101:
						if (RV32B != 32'sd0) begin
							if (instr_alu[26] == 1'b1) begin
								alu_operator_o = 7'd48;
								alu_multicycle_o = 1'b1;
								if (instr_first_cycle_i)
									use_rs3_d = 1'b1;
								else
									use_rs3_d = 1'b0;
							end
							else
								case (instr_alu[31:27])
									5'b00000: alu_operator_o = 7'd9;
									5'b01000: alu_operator_o = 7'd8;
									5'b00100:
										if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
											alu_operator_o = 7'd11;
									5'b01001: alu_operator_o = 7'd52;
									5'b01100: begin
										alu_operator_o = 7'd13;
										alu_multicycle_o = 1'b1;
									end
									5'b01101: alu_operator_o = 7'd15;
									5'b00101: alu_operator_o = 7'd16;
									5'b00001:
										if ((RV32B == 32'sd2) || (RV32B == 32'sd3)) begin
											if (instr_alu[26] == 1'b0)
												alu_operator_o = 7'd18;
										end
									default:
										;
								endcase
						end
						else if (instr_alu[31:27] == 5'b00000)
							alu_operator_o = 7'd9;
						else if (instr_alu[31:27] == 5'b01000)
							alu_operator_o = 7'd8;
					default:
						;
				endcase
			end
			7'h33: begin
				alu_op_a_mux_sel_o = 2'd0;
				alu_op_b_mux_sel_o = 1'd0;
				if (instr_alu[26]) begin
					if (RV32B != 32'sd0)
						case ({instr_alu[26:25], instr_alu[14:12]})
							5'b11001: begin
								alu_operator_o = 7'd46;
								alu_multicycle_o = 1'b1;
								if (instr_first_cycle_i)
									use_rs3_d = 1'b1;
								else
									use_rs3_d = 1'b0;
							end
							5'b11101: begin
								alu_operator_o = 7'd45;
								alu_multicycle_o = 1'b1;
								if (instr_first_cycle_i)
									use_rs3_d = 1'b1;
								else
									use_rs3_d = 1'b0;
							end
							5'b10001: begin
								alu_operator_o = 7'd47;
								alu_multicycle_o = 1'b1;
								if (instr_first_cycle_i)
									use_rs3_d = 1'b1;
								else
									use_rs3_d = 1'b0;
							end
							5'b10101: begin
								alu_operator_o = 7'd48;
								alu_multicycle_o = 1'b1;
								if (instr_first_cycle_i)
									use_rs3_d = 1'b1;
								else
									use_rs3_d = 1'b0;
							end
							default:
								;
						endcase
				end
				else
					case ({instr_alu[31:25], instr_alu[14:12]})
						10'b0000000000: alu_operator_o = 7'd0;
						10'b0100000000: alu_operator_o = 7'd1;
						10'b0000000010: alu_operator_o = 7'd43;
						10'b0000000011: alu_operator_o = 7'd44;
						10'b0000000100: alu_operator_o = 7'd2;
						10'b0000000110: alu_operator_o = 7'd3;
						10'b0000000111: alu_operator_o = 7'd4;
						10'b0000000001: alu_operator_o = 7'd10;
						10'b0000000101: alu_operator_o = 7'd9;
						10'b0100000101: alu_operator_o = 7'd8;
						10'b0110000001:
							if (RV32B != 32'sd0) begin
								alu_operator_o = 7'd14;
								alu_multicycle_o = 1'b1;
							end
						10'b0110000101:
							if (RV32B != 32'sd0) begin
								alu_operator_o = 7'd13;
								alu_multicycle_o = 1'b1;
							end
						10'b0000101100:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd31;
						10'b0000101110:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd33;
						10'b0000101101:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd32;
						10'b0000101111:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd34;
						10'b0000100100:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd35;
						10'b0100100100:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd36;
						10'b0000100111:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd37;
						10'b0100000100:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd5;
						10'b0100000110:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd6;
						10'b0100000111:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd7;
						10'b0010000010:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd22;
						10'b0010000100:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd23;
						10'b0010000110:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd24;
						10'b0100100001:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd50;
						10'b0010100001:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd49;
						10'b0110100001:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd51;
						10'b0100100101:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd52;
						10'b0100100111:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd55;
						10'b0110100101:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd15;
						10'b0010100101:
							if (RV32B != 32'sd0)
								alu_operator_o = 7'd16;
						10'b0000100001:
							if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
								alu_operator_o = 7'd17;
						10'b0000100101:
							if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
								alu_operator_o = 7'd18;
						10'b0010100010:
							if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
								alu_operator_o = 7'd19;
						10'b0010100100:
							if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
								alu_operator_o = 7'd20;
						10'b0010100110:
							if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
								alu_operator_o = 7'd21;
						10'b0010000001:
							if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
								alu_operator_o = 7'd12;
						10'b0010000101:
							if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
								alu_operator_o = 7'd11;
						10'b0000101001:
							if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
								alu_operator_o = 7'd56;
						10'b0000101010:
							if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
								alu_operator_o = 7'd57;
						10'b0000101011:
							if ((RV32B == 32'sd2) || (RV32B == 32'sd3))
								alu_operator_o = 7'd58;
						10'b0100100110:
							if (RV32B == 32'sd3) begin
								alu_operator_o = 7'd54;
								alu_multicycle_o = 1'b1;
							end
						10'b0000100110:
							if (RV32B == 32'sd3) begin
								alu_operator_o = 7'd53;
								alu_multicycle_o = 1'b1;
							end
						10'b0000001000: begin
							alu_operator_o = 7'd0;
							mult_sel_o = (RV32M == 32'sd0 ? 1'b0 : 1'b1);
						end
						10'b0000001001: begin
							alu_operator_o = 7'd0;
							mult_sel_o = (RV32M == 32'sd0 ? 1'b0 : 1'b1);
						end
						10'b0000001010: begin
							alu_operator_o = 7'd0;
							mult_sel_o = (RV32M == 32'sd0 ? 1'b0 : 1'b1);
						end
						10'b0000001011: begin
							alu_operator_o = 7'd0;
							mult_sel_o = (RV32M == 32'sd0 ? 1'b0 : 1'b1);
						end
						10'b0000001100: begin
							alu_operator_o = 7'd0;
							div_sel_o = (RV32M == 32'sd0 ? 1'b0 : 1'b1);
						end
						10'b0000001101: begin
							alu_operator_o = 7'd0;
							div_sel_o = (RV32M == 32'sd0 ? 1'b0 : 1'b1);
						end
						10'b0000001110: begin
							alu_operator_o = 7'd0;
							div_sel_o = (RV32M == 32'sd0 ? 1'b0 : 1'b1);
						end
						10'b0000001111: begin
							alu_operator_o = 7'd0;
							div_sel_o = (RV32M == 32'sd0 ? 1'b0 : 1'b1);
						end
						default:
							;
					endcase
			end
			7'h0f:
				case (instr_alu[14:12])
					3'b000: begin
						alu_operator_o = 7'd0;
						alu_op_a_mux_sel_o = 2'd0;
						alu_op_b_mux_sel_o = 1'd1;
					end
					3'b001:
						if (BranchTargetALU) begin
							bt_a_mux_sel_o = 2'd2;
							bt_b_mux_sel_o = 3'd5;
						end
						else begin
							alu_op_a_mux_sel_o = 2'd2;
							alu_op_b_mux_sel_o = 1'd1;
							imm_b_mux_sel_o = 3'd5;
							alu_operator_o = 7'd0;
						end
					default:
						;
				endcase
			7'h73:
				if (instr_alu[14:12] == 3'b000) begin
					alu_op_a_mux_sel_o = 2'd0;
					alu_op_b_mux_sel_o = 1'd1;
				end
				else begin
					alu_op_b_mux_sel_o = 1'd1;
					imm_a_mux_sel_o = 1'd0;
					imm_b_mux_sel_o = 3'd0;
					if (instr_alu[14])
						alu_op_a_mux_sel_o = 2'd3;
					else
						alu_op_a_mux_sel_o = 2'd0;
				end
			default:
				;
		endcase
	end
	assign mult_en_o = (illegal_insn ? 1'b0 : mult_sel_o);
	assign div_en_o = (illegal_insn ? 1'b0 : div_sel_o);
	assign illegal_insn_o = illegal_insn | illegal_reg_rv32e;
	assign rf_we_o = rf_we & ~illegal_reg_rv32e;
	assign unused_instr_alu = {instr_alu[19:15], instr_alu[11:7]};
endmodule
module ibex_compressed_decoder (
	clk_i,
	rst_ni,
	valid_i,
	instr_i,
	instr_o,
	is_compressed_o,
	illegal_instr_o
);
	input wire clk_i;
	input wire rst_ni;
	input wire valid_i;
	input wire [31:0] instr_i;
	output reg [31:0] instr_o;
	output wire is_compressed_o;
	output reg illegal_instr_o;
	wire unused_valid;
	assign unused_valid = valid_i;
	always @(*) begin
		instr_o = instr_i;
		illegal_instr_o = 1'b0;
		case (instr_i[1:0])
			2'b00:
				case (instr_i[15:13])
					3'b000: begin
						instr_o = {2'b00, instr_i[10:7], instr_i[12:11], instr_i[5], instr_i[6], 12'h041, instr_i[4:2], 7'h13};
						if (instr_i[12:5] == 8'b00000000)
							illegal_instr_o = 1'b1;
					end
					3'b010: instr_o = {5'b00000, instr_i[5], instr_i[12:10], instr_i[6], 4'b0001, instr_i[9:7], 5'b01001, instr_i[4:2], 7'h03};
					3'b110: instr_o = {5'b00000, instr_i[5], instr_i[12], 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b010, instr_i[11:10], instr_i[6], 9'h023};
					3'b001, 3'b011, 3'b100, 3'b101, 3'b111: illegal_instr_o = 1'b1;
					default: illegal_instr_o = 1'b1;
				endcase
			2'b01:
				case (instr_i[15:13])
					3'b000: instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], instr_i[11:7], 3'b000, instr_i[11:7], 7'h13};
					3'b001, 3'b101: instr_o = {instr_i[12], instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], instr_i[2], instr_i[11], instr_i[5:3], {9 {instr_i[12]}}, 4'b0000, ~instr_i[15], 7'h6f};
					3'b010: instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 8'b00000000, instr_i[11:7], 7'h13};
					3'b011: begin
						instr_o = {{15 {instr_i[12]}}, instr_i[6:2], instr_i[11:7], 7'h37};
						if (instr_i[11:7] == 5'h02)
							instr_o = {{3 {instr_i[12]}}, instr_i[4:3], instr_i[5], instr_i[2], instr_i[6], 24'h010113};
						if ({instr_i[12], instr_i[6:2]} == 6'b000000)
							illegal_instr_o = 1'b1;
					end
					3'b100:
						case (instr_i[11:10])
							2'b00, 2'b01: begin
								instr_o = {1'b0, instr_i[10], 5'b00000, instr_i[6:2], 2'b01, instr_i[9:7], 5'b10101, instr_i[9:7], 7'h13};
								if (instr_i[12] == 1'b1)
									illegal_instr_o = 1'b1;
							end
							2'b10: instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 2'b01, instr_i[9:7], 5'b11101, instr_i[9:7], 7'h13};
							2'b11:
								case ({instr_i[12], instr_i[6:5]})
									3'b000: instr_o = {9'b010000001, instr_i[4:2], 2'b01, instr_i[9:7], 5'b00001, instr_i[9:7], 7'h33};
									3'b001: instr_o = {9'b000000001, instr_i[4:2], 2'b01, instr_i[9:7], 5'b10001, instr_i[9:7], 7'h33};
									3'b010: instr_o = {9'b000000001, instr_i[4:2], 2'b01, instr_i[9:7], 5'b11001, instr_i[9:7], 7'h33};
									3'b011: instr_o = {9'b000000001, instr_i[4:2], 2'b01, instr_i[9:7], 5'b11101, instr_i[9:7], 7'h33};
									3'b100, 3'b101, 3'b110, 3'b111: illegal_instr_o = 1'b1;
									default: illegal_instr_o = 1'b1;
								endcase
							default: illegal_instr_o = 1'b1;
						endcase
					3'b110, 3'b111: instr_o = {{4 {instr_i[12]}}, instr_i[6:5], instr_i[2], 7'b0000001, instr_i[9:7], 2'b00, instr_i[13], instr_i[11:10], instr_i[4:3], instr_i[12], 7'h63};
					default: illegal_instr_o = 1'b1;
				endcase
			2'b10:
				case (instr_i[15:13])
					3'b000: begin
						instr_o = {7'b0000000, instr_i[6:2], instr_i[11:7], 3'b001, instr_i[11:7], 7'h13};
						if (instr_i[12] == 1'b1)
							illegal_instr_o = 1'b1;
					end
					3'b010: begin
						instr_o = {4'b0000, instr_i[3:2], instr_i[12], instr_i[6:4], 10'h012, instr_i[11:7], 7'h03};
						if (instr_i[11:7] == 5'b00000)
							illegal_instr_o = 1'b1;
					end
					3'b100:
						if (instr_i[12] == 1'b0) begin
							if (instr_i[6:2] != 5'b00000)
								instr_o = {7'b0000000, instr_i[6:2], 8'b00000000, instr_i[11:7], 7'h33};
							else begin
								instr_o = {12'b000000000000, instr_i[11:7], 15'h0067};
								if (instr_i[11:7] == 5'b00000)
									illegal_instr_o = 1'b1;
							end
						end
						else if (instr_i[6:2] != 5'b00000)
							instr_o = {7'b0000000, instr_i[6:2], instr_i[11:7], 3'b000, instr_i[11:7], 7'h33};
						else if (instr_i[11:7] == 5'b00000)
							instr_o = 32'h00100073;
						else
							instr_o = {12'b000000000000, instr_i[11:7], 15'h00e7};
					3'b110: instr_o = {4'b0000, instr_i[8:7], instr_i[12], instr_i[6:2], 8'h12, instr_i[11:9], 9'h023};
					3'b001, 3'b011, 3'b101, 3'b111: illegal_instr_o = 1'b1;
					default: illegal_instr_o = 1'b1;
				endcase
			2'b11:
				;
			default: illegal_instr_o = 1'b1;
		endcase
	end
	assign is_compressed_o = instr_i[1:0] != 2'b11;
endmodule
module prim_generic_buf (
	in_i,
	out_o
);
	parameter signed [31:0] Width = 1;
	input [Width - 1:0] in_i;
	output wire [Width - 1:0] out_o;
	wire [Width - 1:0] inv;
	assign inv = ~in_i;
	assign out_o = ~inv;
endmodule
module ibex_cs_registers (
	clk_i,
	rst_ni,
	hart_id_i,
	priv_mode_id_o,
	priv_mode_lsu_o,
	csr_mstatus_tw_o,
	csr_mtvec_o,
	csr_mtvec_init_i,
	boot_addr_i,
	csr_access_i,
	csr_addr_i,
	csr_wdata_i,
	csr_op_i,
	csr_op_en_i,
	csr_rdata_o,
	irq_software_i,
	irq_timer_i,
	irq_external_i,
	irq_fast_i,
	nmi_mode_i,
	irq_pending_o,
	irqs_o,
	csr_mstatus_mie_o,
	csr_mepc_o,
	csr_mtval_o,
	csr_pmp_cfg_o,
	csr_pmp_addr_o,
	csr_pmp_mseccfg_o,
	debug_mode_i,
	debug_mode_entering_i,
	debug_cause_i,
	debug_csr_save_i,
	csr_depc_o,
	debug_single_step_o,
	debug_ebreakm_o,
	debug_ebreaku_o,
	trigger_match_o,
	pc_if_i,
	pc_id_i,
	pc_wb_i,
	data_ind_timing_o,
	dummy_instr_en_o,
	dummy_instr_mask_o,
	dummy_instr_seed_en_o,
	dummy_instr_seed_o,
	icache_enable_o,
	csr_shadow_err_o,
	ic_scr_key_valid_i,
	csr_save_if_i,
	csr_save_id_i,
	csr_save_wb_i,
	csr_restore_mret_i,
	csr_restore_dret_i,
	csr_save_cause_i,
	csr_mcause_i,
	csr_mtval_i,
	illegal_csr_insn_o,
	double_fault_seen_o,
	instr_ret_i,
	instr_ret_compressed_i,
	instr_ret_spec_i,
	instr_ret_compressed_spec_i,
	iside_wait_i,
	jump_i,
	branch_i,
	branch_taken_i,
	mem_load_i,
	mem_store_i,
	dside_wait_i,
	mul_wait_i,
	div_wait_i
);
	parameter [0:0] DbgTriggerEn = 0;
	parameter [31:0] DbgHwBreakNum = 1;
	parameter [0:0] DataIndTiming = 1'b0;
	parameter [0:0] DummyInstructions = 1'b0;
	parameter [0:0] ShadowCSR = 1'b0;
	parameter [0:0] ICache = 1'b0;
	parameter [31:0] MHPMCounterNum = 10;
	parameter [31:0] MHPMCounterWidth = 40;
	parameter [0:0] PMPEnable = 0;
	parameter [31:0] PMPGranularity = 0;
	parameter [31:0] PMPNumRegions = 4;
	parameter [0:0] RV32E = 0;
	parameter integer RV32M = 32'sd2;
	parameter integer RV32B = 32'sd0;
	input wire clk_i;
	input wire rst_ni;
	input wire [31:0] hart_id_i;
	output wire [1:0] priv_mode_id_o;
	output wire [1:0] priv_mode_lsu_o;
	output wire csr_mstatus_tw_o;
	output wire [31:0] csr_mtvec_o;
	input wire csr_mtvec_init_i;
	input wire [31:0] boot_addr_i;
	input wire csr_access_i;
	input wire [11:0] csr_addr_i;
	input wire [31:0] csr_wdata_i;
	input wire [1:0] csr_op_i;
	input csr_op_en_i;
	output wire [31:0] csr_rdata_o;
	input wire irq_software_i;
	input wire irq_timer_i;
	input wire irq_external_i;
	input wire [14:0] irq_fast_i;
	input wire nmi_mode_i;
	output wire irq_pending_o;
	output wire [17:0] irqs_o;
	output wire csr_mstatus_mie_o;
	output wire [31:0] csr_mepc_o;
	output wire [31:0] csr_mtval_o;
	output wire [(PMPNumRegions * 6) - 1:0] csr_pmp_cfg_o;
	output wire [(PMPNumRegions * 34) - 1:0] csr_pmp_addr_o;
	output wire [2:0] csr_pmp_mseccfg_o;
	input wire debug_mode_i;
	input wire debug_mode_entering_i;
	input wire [2:0] debug_cause_i;
	input wire debug_csr_save_i;
	output wire [31:0] csr_depc_o;
	output wire debug_single_step_o;
	output wire debug_ebreakm_o;
	output wire debug_ebreaku_o;
	output wire trigger_match_o;
	input wire [31:0] pc_if_i;
	input wire [31:0] pc_id_i;
	input wire [31:0] pc_wb_i;
	output wire data_ind_timing_o;
	output wire dummy_instr_en_o;
	output wire [2:0] dummy_instr_mask_o;
	output wire dummy_instr_seed_en_o;
	output wire [31:0] dummy_instr_seed_o;
	output wire icache_enable_o;
	output wire csr_shadow_err_o;
	input wire ic_scr_key_valid_i;
	input wire csr_save_if_i;
	input wire csr_save_id_i;
	input wire csr_save_wb_i;
	input wire csr_restore_mret_i;
	input wire csr_restore_dret_i;
	input wire csr_save_cause_i;
	input wire [6:0] csr_mcause_i;
	input wire [31:0] csr_mtval_i;
	output wire illegal_csr_insn_o;
	output reg double_fault_seen_o;
	input wire instr_ret_i;
	input wire instr_ret_compressed_i;
	input wire instr_ret_spec_i;
	input wire instr_ret_compressed_spec_i;
	input wire iside_wait_i;
	input wire jump_i;
	input wire branch_i;
	input wire branch_taken_i;
	input wire mem_load_i;
	input wire mem_store_i;
	input wire dside_wait_i;
	input wire mul_wait_i;
	input wire div_wait_i;
	function automatic is_mml_m_exec_cfg;
		input reg [5:0] pmp_cfg;
		reg unused_cfg;
		reg value;
		begin
			unused_cfg = ^{pmp_cfg[4-:2]};
			value = 1'b0;
			if (pmp_cfg[5])
				case ({pmp_cfg[0], pmp_cfg[1], pmp_cfg[2]})
					3'b001, 3'b010, 3'b011, 3'b101: value = 1'b1;
					default: value = 1'b0;
				endcase
			is_mml_m_exec_cfg = value;
		end
	endfunction
	localparam [31:0] RV32BExtra = (RV32B != 32'sd0 ? 1 : 0);
	localparam [31:0] RV32MEnabled = (RV32M == 32'sd0 ? 0 : 1);
	localparam [31:0] PMPAddrWidth = (PMPGranularity > 0 ? 33 - PMPGranularity : 32);
	localparam [1:0] ibex_pkg_CSR_MISA_MXL = 2'd1;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	localparam [31:0] MISA_VALUE = ((((((((4 | (sv2v_cast_32(RV32E) << 4)) | 0) | (sv2v_cast_32(!RV32E) << 8)) | (RV32MEnabled << 12)) | 0) | 0) | 1048576) | (RV32BExtra << 23)) | (sv2v_cast_32(ibex_pkg_CSR_MISA_MXL) << 30);
	reg [31:0] exception_pc;
	reg [1:0] priv_lvl_q;
	reg [1:0] priv_lvl_d;
	wire [5:0] mstatus_q;
	reg [5:0] mstatus_d;
	wire mstatus_err;
	reg mstatus_en;
	wire [17:0] mie_q;
	wire [17:0] mie_d;
	reg mie_en;
	wire [31:0] mscratch_q;
	reg mscratch_en;
	wire [31:0] mepc_q;
	reg [31:0] mepc_d;
	reg mepc_en;
	wire [6:0] mcause_q;
	reg [6:0] mcause_d;
	reg mcause_en;
	wire [31:0] mtval_q;
	reg [31:0] mtval_d;
	reg mtval_en;
	wire [31:0] mtvec_q;
	reg [31:0] mtvec_d;
	wire mtvec_err;
	reg mtvec_en;
	wire [17:0] mip;
	wire [31:0] dcsr_q;
	reg [31:0] dcsr_d;
	reg dcsr_en;
	wire [31:0] depc_q;
	reg [31:0] depc_d;
	reg depc_en;
	wire [31:0] dscratch0_q;
	wire [31:0] dscratch1_q;
	reg dscratch0_en;
	reg dscratch1_en;
	wire [2:0] mstack_q;
	reg [2:0] mstack_d;
	reg mstack_en;
	wire [31:0] mstack_epc_q;
	reg [31:0] mstack_epc_d;
	wire [6:0] mstack_cause_q;
	reg [6:0] mstack_cause_d;
	localparam [31:0] ibex_pkg_PMP_MAX_REGIONS = 16;
	reg [31:0] pmp_addr_rdata [0:15];
	localparam [31:0] ibex_pkg_PMP_CFG_W = 8;
	wire [7:0] pmp_cfg_rdata [0:15];
	wire pmp_csr_err;
	wire [2:0] pmp_mseccfg;
	wire [31:0] mcountinhibit;
	reg [MHPMCounterNum + 2:0] mcountinhibit_d;
	reg [MHPMCounterNum + 2:0] mcountinhibit_q;
	reg mcountinhibit_we;
	wire [63:0] mhpmcounter [0:31];
	reg [31:0] mhpmcounter_we;
	reg [31:0] mhpmcounterh_we;
	reg [31:0] mhpmcounter_incr;
	reg [31:0] mhpmevent [0:31];
	wire [4:0] mhpmcounter_idx;
	wire unused_mhpmcounter_we_1;
	wire unused_mhpmcounterh_we_1;
	wire unused_mhpmcounter_incr_1;
	wire [63:0] minstret_next;
	wire [63:0] minstret_raw;
	wire [31:0] tselect_rdata;
	wire [31:0] tmatch_control_rdata;
	wire [31:0] tmatch_value_rdata;
	wire [7:0] cpuctrlsts_part_q;
	reg [7:0] cpuctrlsts_part_d;
	wire [7:0] cpuctrlsts_part_wdata_raw;
	wire [7:0] cpuctrlsts_part_wdata;
	reg cpuctrlsts_part_we;
	wire cpuctrlsts_part_err;
	wire cpuctrlsts_ic_scr_key_valid_q;
	wire cpuctrlsts_ic_scr_key_err;
	reg [31:0] csr_wdata_int;
	reg [31:0] csr_rdata_int;
	wire csr_we_int;
	wire csr_wr;
	reg dbg_csr;
	reg illegal_csr;
	wire illegal_csr_priv;
	wire illegal_csr_dbg;
	wire illegal_csr_write;
	wire [7:0] unused_boot_addr;
	wire [2:0] unused_csr_addr;
	assign unused_boot_addr = boot_addr_i[7:0];
	wire [11:0] csr_addr;
	assign csr_addr = {csr_addr_i};
	assign unused_csr_addr = csr_addr[7:5];
	assign mhpmcounter_idx = csr_addr[4:0];
	assign illegal_csr_dbg = dbg_csr & ~debug_mode_i;
	assign illegal_csr_priv = csr_addr[9:8] > {priv_lvl_q};
	assign illegal_csr_write = (csr_addr[11:10] == 2'b11) && csr_wr;
	assign illegal_csr_insn_o = csr_access_i & (((illegal_csr | illegal_csr_write) | illegal_csr_priv) | illegal_csr_dbg);
	assign mip[17] = irq_software_i;
	assign mip[16] = irq_timer_i;
	assign mip[15] = irq_external_i;
	assign mip[14-:15] = irq_fast_i;
	localparam [31:0] ibex_pkg_CSR_MARCHID_VALUE = 32'h00000016;
	localparam [31:0] ibex_pkg_CSR_MCONFIGPTR_VALUE = 32'b00000000000000000000000000000000;
	localparam [31:0] ibex_pkg_CSR_MEIX_BIT = 11;
	localparam [31:0] ibex_pkg_CSR_MFIX_BIT_HIGH = 30;
	localparam [31:0] ibex_pkg_CSR_MFIX_BIT_LOW = 16;
	localparam [31:0] ibex_pkg_CSR_MIMPID_VALUE = 32'b00000000000000000000000000000000;
	localparam [31:0] ibex_pkg_CSR_MSECCFG_MML_BIT = 0;
	localparam [31:0] ibex_pkg_CSR_MSECCFG_MMWP_BIT = 1;
	localparam [31:0] ibex_pkg_CSR_MSECCFG_RLB_BIT = 2;
	localparam [31:0] ibex_pkg_CSR_MSIX_BIT = 3;
	localparam [31:0] ibex_pkg_CSR_MSTATUS_MIE_BIT = 3;
	localparam [31:0] ibex_pkg_CSR_MSTATUS_MPIE_BIT = 7;
	localparam [31:0] ibex_pkg_CSR_MSTATUS_MPP_BIT_HIGH = 12;
	localparam [31:0] ibex_pkg_CSR_MSTATUS_MPP_BIT_LOW = 11;
	localparam [31:0] ibex_pkg_CSR_MSTATUS_MPRV_BIT = 17;
	localparam [31:0] ibex_pkg_CSR_MSTATUS_TW_BIT = 21;
	localparam [31:0] ibex_pkg_CSR_MTIX_BIT = 7;
	localparam [31:0] ibex_pkg_CSR_MVENDORID_VALUE = 32'b00000000000000000000000000000000;
	always @(*) begin
		csr_rdata_int = 1'sb0;
		illegal_csr = 1'b0;
		dbg_csr = 1'b0;
		case (csr_addr_i)
			12'hf11: csr_rdata_int = ibex_pkg_CSR_MVENDORID_VALUE;
			12'hf12: csr_rdata_int = ibex_pkg_CSR_MARCHID_VALUE;
			12'hf13: csr_rdata_int = ibex_pkg_CSR_MIMPID_VALUE;
			12'hf14: csr_rdata_int = hart_id_i;
			12'hf15: csr_rdata_int = ibex_pkg_CSR_MCONFIGPTR_VALUE;
			12'h300: begin
				csr_rdata_int = 1'sb0;
				csr_rdata_int[ibex_pkg_CSR_MSTATUS_MIE_BIT] = mstatus_q[5];
				csr_rdata_int[ibex_pkg_CSR_MSTATUS_MPIE_BIT] = mstatus_q[4];
				csr_rdata_int[ibex_pkg_CSR_MSTATUS_MPP_BIT_HIGH:ibex_pkg_CSR_MSTATUS_MPP_BIT_LOW] = mstatus_q[3-:2];
				csr_rdata_int[ibex_pkg_CSR_MSTATUS_MPRV_BIT] = mstatus_q[1];
				csr_rdata_int[ibex_pkg_CSR_MSTATUS_TW_BIT] = mstatus_q[0];
			end
			12'h310: csr_rdata_int = 1'sb0;
			12'h30a, 12'h31a: csr_rdata_int = 1'sb0;
			12'h301: csr_rdata_int = MISA_VALUE;
			12'h304: begin
				csr_rdata_int = 1'sb0;
				csr_rdata_int[ibex_pkg_CSR_MSIX_BIT] = mie_q[17];
				csr_rdata_int[ibex_pkg_CSR_MTIX_BIT] = mie_q[16];
				csr_rdata_int[ibex_pkg_CSR_MEIX_BIT] = mie_q[15];
				csr_rdata_int[ibex_pkg_CSR_MFIX_BIT_HIGH:ibex_pkg_CSR_MFIX_BIT_LOW] = mie_q[14-:15];
			end
			12'h306: csr_rdata_int = 1'sb0;
			12'h340: csr_rdata_int = mscratch_q;
			12'h305: csr_rdata_int = mtvec_q;
			12'h341: csr_rdata_int = mepc_q;
			12'h342: csr_rdata_int = {mcause_q[5] | mcause_q[6], (mcause_q[6] ? {26 {1'b1}} : 26'b00000000000000000000000000), mcause_q[4:0]};
			12'h343: csr_rdata_int = mtval_q;
			12'h344: begin
				csr_rdata_int = 1'sb0;
				csr_rdata_int[ibex_pkg_CSR_MSIX_BIT] = mip[17];
				csr_rdata_int[ibex_pkg_CSR_MTIX_BIT] = mip[16];
				csr_rdata_int[ibex_pkg_CSR_MEIX_BIT] = mip[15];
				csr_rdata_int[ibex_pkg_CSR_MFIX_BIT_HIGH:ibex_pkg_CSR_MFIX_BIT_LOW] = mip[14-:15];
			end
			12'h747:
				if (PMPEnable) begin
					csr_rdata_int = 1'sb0;
					csr_rdata_int[ibex_pkg_CSR_MSECCFG_MML_BIT] = pmp_mseccfg[0];
					csr_rdata_int[ibex_pkg_CSR_MSECCFG_MMWP_BIT] = pmp_mseccfg[1];
					csr_rdata_int[ibex_pkg_CSR_MSECCFG_RLB_BIT] = pmp_mseccfg[2];
				end
				else
					illegal_csr = 1'b1;
			12'h757:
				if (PMPEnable)
					csr_rdata_int = 1'sb0;
				else
					illegal_csr = 1'b1;
			12'h3a0: csr_rdata_int = {pmp_cfg_rdata[3], pmp_cfg_rdata[2], pmp_cfg_rdata[1], pmp_cfg_rdata[0]};
			12'h3a1: csr_rdata_int = {pmp_cfg_rdata[7], pmp_cfg_rdata[6], pmp_cfg_rdata[5], pmp_cfg_rdata[4]};
			12'h3a2: csr_rdata_int = {pmp_cfg_rdata[11], pmp_cfg_rdata[10], pmp_cfg_rdata[9], pmp_cfg_rdata[8]};
			12'h3a3: csr_rdata_int = {pmp_cfg_rdata[15], pmp_cfg_rdata[14], pmp_cfg_rdata[13], pmp_cfg_rdata[12]};
			12'h3b0: csr_rdata_int = pmp_addr_rdata[0];
			12'h3b1: csr_rdata_int = pmp_addr_rdata[1];
			12'h3b2: csr_rdata_int = pmp_addr_rdata[2];
			12'h3b3: csr_rdata_int = pmp_addr_rdata[3];
			12'h3b4: csr_rdata_int = pmp_addr_rdata[4];
			12'h3b5: csr_rdata_int = pmp_addr_rdata[5];
			12'h3b6: csr_rdata_int = pmp_addr_rdata[6];
			12'h3b7: csr_rdata_int = pmp_addr_rdata[7];
			12'h3b8: csr_rdata_int = pmp_addr_rdata[8];
			12'h3b9: csr_rdata_int = pmp_addr_rdata[9];
			12'h3ba: csr_rdata_int = pmp_addr_rdata[10];
			12'h3bb: csr_rdata_int = pmp_addr_rdata[11];
			12'h3bc: csr_rdata_int = pmp_addr_rdata[12];
			12'h3bd: csr_rdata_int = pmp_addr_rdata[13];
			12'h3be: csr_rdata_int = pmp_addr_rdata[14];
			12'h3bf: csr_rdata_int = pmp_addr_rdata[15];
			12'h7b0: begin
				csr_rdata_int = dcsr_q;
				dbg_csr = 1'b1;
			end
			12'h7b1: begin
				csr_rdata_int = depc_q;
				dbg_csr = 1'b1;
			end
			12'h7b2: begin
				csr_rdata_int = dscratch0_q;
				dbg_csr = 1'b1;
			end
			12'h7b3: begin
				csr_rdata_int = dscratch1_q;
				dbg_csr = 1'b1;
			end
			12'h320: csr_rdata_int = mcountinhibit;
			12'h323, 12'h324, 12'h325, 12'h326, 12'h327, 12'h328, 12'h329, 12'h32a, 12'h32b, 12'h32c, 12'h32d, 12'h32e, 12'h32f, 12'h330, 12'h331, 12'h332, 12'h333, 12'h334, 12'h335, 12'h336, 12'h337, 12'h338, 12'h339, 12'h33a, 12'h33b, 12'h33c, 12'h33d, 12'h33e, 12'h33f: csr_rdata_int = mhpmevent[mhpmcounter_idx];
			12'hb00, 12'hb02, 12'hb03, 12'hb04, 12'hb05, 12'hb06, 12'hb07, 12'hb08, 12'hb09, 12'hb0a, 12'hb0b, 12'hb0c, 12'hb0d, 12'hb0e, 12'hb0f, 12'hb10, 12'hb11, 12'hb12, 12'hb13, 12'hb14, 12'hb15, 12'hb16, 12'hb17, 12'hb18, 12'hb19, 12'hb1a, 12'hb1b, 12'hb1c, 12'hb1d, 12'hb1e, 12'hb1f: csr_rdata_int = mhpmcounter[mhpmcounter_idx][31:0];
			12'hb80, 12'hb82, 12'hb83, 12'hb84, 12'hb85, 12'hb86, 12'hb87, 12'hb88, 12'hb89, 12'hb8a, 12'hb8b, 12'hb8c, 12'hb8d, 12'hb8e, 12'hb8f, 12'hb90, 12'hb91, 12'hb92, 12'hb93, 12'hb94, 12'hb95, 12'hb96, 12'hb97, 12'hb98, 12'hb99, 12'hb9a, 12'hb9b, 12'hb9c, 12'hb9d, 12'hb9e, 12'hb9f: csr_rdata_int = mhpmcounter[mhpmcounter_idx][63:32];
			12'h7a0: begin
				csr_rdata_int = tselect_rdata;
				illegal_csr = ~DbgTriggerEn;
			end
			12'h7a1: begin
				csr_rdata_int = tmatch_control_rdata;
				illegal_csr = ~DbgTriggerEn;
			end
			12'h7a2: begin
				csr_rdata_int = tmatch_value_rdata;
				illegal_csr = ~DbgTriggerEn;
			end
			12'h7a3: begin
				csr_rdata_int = 1'sb0;
				illegal_csr = ~DbgTriggerEn;
			end
			12'h7a8: begin
				csr_rdata_int = 1'sb0;
				illegal_csr = ~DbgTriggerEn;
			end
			12'h5a8: begin
				csr_rdata_int = 1'sb0;
				illegal_csr = ~DbgTriggerEn;
			end
			12'h7aa: begin
				csr_rdata_int = 1'sb0;
				illegal_csr = ~DbgTriggerEn;
			end
			12'h7c0: csr_rdata_int = {{23 {1'b0}}, cpuctrlsts_ic_scr_key_valid_q, cpuctrlsts_part_q};
			12'h7c1: csr_rdata_int = 1'sb0;
			default: illegal_csr = 1'b1;
		endcase
		if (!PMPEnable) begin
			if (|{csr_addr == 12'h3a0, csr_addr == 12'h3a1, csr_addr == 12'h3a2, csr_addr == 12'h3a3, csr_addr == 12'h3b0, csr_addr == 12'h3b1, csr_addr == 12'h3b2, csr_addr == 12'h3b3, csr_addr == 12'h3b4, csr_addr == 12'h3b5, csr_addr == 12'h3b6, csr_addr == 12'h3b7, csr_addr == 12'h3b8, csr_addr == 12'h3b9, csr_addr == 12'h3ba, csr_addr == 12'h3bb, csr_addr == 12'h3bc, csr_addr == 12'h3bd, csr_addr == 12'h3be, csr_addr == 12'h3bf})
				illegal_csr = 1'b1;
		end
	end
	function automatic [1:0] sv2v_cast_2;
		input reg [1:0] inp;
		sv2v_cast_2 = inp;
	endfunction
	always @(*) begin
		exception_pc = pc_id_i;
		priv_lvl_d = priv_lvl_q;
		mstatus_en = 1'b0;
		mstatus_d = mstatus_q;
		mie_en = 1'b0;
		mscratch_en = 1'b0;
		mepc_en = 1'b0;
		mepc_d = {csr_wdata_int[31:1], 1'b0};
		mcause_en = 1'b0;
		mcause_d = {csr_wdata_int[31:30] == 2'b11, csr_wdata_int[31:30] == 2'b10, csr_wdata_int[4:0]};
		mtval_en = 1'b0;
		mtval_d = csr_wdata_int;
		mtvec_en = csr_mtvec_init_i;
		mtvec_d = (csr_mtvec_init_i ? {boot_addr_i[31:8], 8'b00000001} : {csr_wdata_int[31:8], 8'b00000001});
		dcsr_en = 1'b0;
		dcsr_d = dcsr_q;
		depc_d = {csr_wdata_int[31:1], 1'b0};
		depc_en = 1'b0;
		dscratch0_en = 1'b0;
		dscratch1_en = 1'b0;
		mstack_en = 1'b0;
		mstack_d[2] = mstatus_q[4];
		mstack_d[1-:2] = mstatus_q[3-:2];
		mstack_epc_d = mepc_q;
		mstack_cause_d = mcause_q;
		mcountinhibit_we = 1'b0;
		mhpmcounter_we = 1'sb0;
		mhpmcounterh_we = 1'sb0;
		cpuctrlsts_part_we = 1'b0;
		cpuctrlsts_part_d = cpuctrlsts_part_q;
		double_fault_seen_o = 1'b0;
		if (csr_we_int)
			case (csr_addr_i)
				12'h300: begin
					mstatus_en = 1'b1;
					mstatus_d = {csr_wdata_int[ibex_pkg_CSR_MSTATUS_MIE_BIT], csr_wdata_int[ibex_pkg_CSR_MSTATUS_MPIE_BIT], sv2v_cast_2(csr_wdata_int[ibex_pkg_CSR_MSTATUS_MPP_BIT_HIGH:ibex_pkg_CSR_MSTATUS_MPP_BIT_LOW]), csr_wdata_int[ibex_pkg_CSR_MSTATUS_MPRV_BIT], csr_wdata_int[ibex_pkg_CSR_MSTATUS_TW_BIT]};
					if ((mstatus_d[3-:2] != 2'b11) && (mstatus_d[3-:2] != 2'b00))
						mstatus_d[3-:2] = 2'b00;
				end
				12'h304: mie_en = 1'b1;
				12'h340: mscratch_en = 1'b1;
				12'h341: mepc_en = 1'b1;
				12'h342: mcause_en = 1'b1;
				12'h343: mtval_en = 1'b1;
				12'h305: mtvec_en = 1'b1;
				12'h7b0: begin
					dcsr_d = csr_wdata_int;
					dcsr_d[31-:4] = 4'd4;
					if ((dcsr_d[1-:2] != 2'b11) && (dcsr_d[1-:2] != 2'b00))
						dcsr_d[1-:2] = 2'b00;
					dcsr_d[8-:3] = dcsr_q[8-:3];
					dcsr_d[11] = 1'b0;
					dcsr_d[3] = 1'b0;
					dcsr_d[4] = 1'b0;
					dcsr_d[10] = 1'b0;
					dcsr_d[9] = 1'b0;
					dcsr_d[5] = 1'b0;
					dcsr_d[14] = 1'b0;
					dcsr_d[27-:12] = 12'h000;
					dcsr_en = 1'b1;
				end
				12'h7b1: depc_en = 1'b1;
				12'h7b2: dscratch0_en = 1'b1;
				12'h7b3: dscratch1_en = 1'b1;
				12'h320: mcountinhibit_we = 1'b1;
				12'hb00, 12'hb02, 12'hb03, 12'hb04, 12'hb05, 12'hb06, 12'hb07, 12'hb08, 12'hb09, 12'hb0a, 12'hb0b, 12'hb0c, 12'hb0d, 12'hb0e, 12'hb0f, 12'hb10, 12'hb11, 12'hb12, 12'hb13, 12'hb14, 12'hb15, 12'hb16, 12'hb17, 12'hb18, 12'hb19, 12'hb1a, 12'hb1b, 12'hb1c, 12'hb1d, 12'hb1e, 12'hb1f: mhpmcounter_we[mhpmcounter_idx] = 1'b1;
				12'hb80, 12'hb82, 12'hb83, 12'hb84, 12'hb85, 12'hb86, 12'hb87, 12'hb88, 12'hb89, 12'hb8a, 12'hb8b, 12'hb8c, 12'hb8d, 12'hb8e, 12'hb8f, 12'hb90, 12'hb91, 12'hb92, 12'hb93, 12'hb94, 12'hb95, 12'hb96, 12'hb97, 12'hb98, 12'hb99, 12'hb9a, 12'hb9b, 12'hb9c, 12'hb9d, 12'hb9e, 12'hb9f: mhpmcounterh_we[mhpmcounter_idx] = 1'b1;
				12'h7c0: begin
					cpuctrlsts_part_d = cpuctrlsts_part_wdata;
					cpuctrlsts_part_we = 1'b1;
				end
				default:
					;
			endcase
		case (1'b1)
			csr_save_cause_i: begin
				case (1'b1)
					csr_save_if_i: exception_pc = pc_if_i;
					csr_save_id_i: exception_pc = pc_id_i;
					csr_save_wb_i: exception_pc = pc_wb_i;
					default:
						;
				endcase
				priv_lvl_d = 2'b11;
				if (debug_csr_save_i) begin
					dcsr_d[1-:2] = priv_lvl_q;
					dcsr_d[8-:3] = debug_cause_i;
					dcsr_en = 1'b1;
					depc_d = exception_pc;
					depc_en = 1'b1;
				end
				else if (!debug_mode_i) begin
					mtval_en = 1'b1;
					mtval_d = csr_mtval_i;
					mstatus_en = 1'b1;
					mstatus_d[5] = 1'b0;
					mstatus_d[4] = mstatus_q[5];
					mstatus_d[3-:2] = priv_lvl_q;
					mepc_en = 1'b1;
					mepc_d = exception_pc;
					mcause_en = 1'b1;
					mcause_d = csr_mcause_i;
					mstack_en = 1'b1;
					if (!(mcause_d[5] || mcause_d[6])) begin
						cpuctrlsts_part_we = 1'b1;
						cpuctrlsts_part_d[6] = 1'b1;
						if (cpuctrlsts_part_q[6]) begin
							double_fault_seen_o = 1'b1;
							cpuctrlsts_part_d[7] = 1'b1;
						end
					end
				end
			end
			csr_restore_dret_i: priv_lvl_d = dcsr_q[1-:2];
			csr_restore_mret_i: begin
				priv_lvl_d = mstatus_q[3-:2];
				mstatus_en = 1'b1;
				mstatus_d[5] = mstatus_q[4];
				if (mstatus_q[3-:2] != 2'b11)
					mstatus_d[1] = 1'b0;
				cpuctrlsts_part_we = 1'b1;
				cpuctrlsts_part_d[6] = 1'b0;
				if (nmi_mode_i) begin
					mstatus_d[4] = mstack_q[2];
					mstatus_d[3-:2] = mstack_q[1-:2];
					mepc_en = 1'b1;
					mepc_d = mstack_epc_q;
					mcause_en = 1'b1;
					mcause_d = mstack_cause_q;
				end
				else begin
					mstatus_d[4] = 1'b1;
					mstatus_d[3-:2] = 2'b00;
				end
			end
			default:
				;
		endcase
	end
	always @(posedge clk_i)
		if (!rst_ni)
			priv_lvl_q <= 2'b11;
		else
			priv_lvl_q <= priv_lvl_d;
	assign priv_mode_id_o = priv_lvl_q;
	assign priv_mode_lsu_o = (mstatus_q[1] ? mstatus_q[3-:2] : priv_lvl_q);
	always @(*)
		case (csr_op_i)
			2'd1: csr_wdata_int = csr_wdata_i;
			2'd2: csr_wdata_int = csr_wdata_i | csr_rdata_o;
			2'd3: csr_wdata_int = ~csr_wdata_i & csr_rdata_o;
			2'd0: csr_wdata_int = csr_wdata_i;
			default: csr_wdata_int = csr_wdata_i;
		endcase
	assign csr_wr = |{csr_op_i == 2'd1, csr_op_i == 2'd2, csr_op_i == 2'd3};
	assign csr_we_int = (csr_wr & csr_op_en_i) & ~illegal_csr_insn_o;
	assign csr_rdata_o = csr_rdata_int;
	assign csr_mepc_o = mepc_q;
	assign csr_depc_o = depc_q;
	assign csr_mtvec_o = mtvec_q;
	assign csr_mtval_o = mtval_q;
	assign csr_mstatus_mie_o = mstatus_q[5];
	assign csr_mstatus_tw_o = mstatus_q[0];
	assign debug_single_step_o = dcsr_q[2];
	assign debug_ebreakm_o = dcsr_q[15];
	assign debug_ebreaku_o = dcsr_q[12];
	assign irqs_o = mip & mie_q;
	assign irq_pending_o = |irqs_o;
	localparam [5:0] MSTATUS_RST_VAL = 6'b010000;
	ibex_csr #(
		.Width(6),
		.ShadowCopy(ShadowCSR),
		.ResetValue({MSTATUS_RST_VAL})
	) u_mstatus_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i({mstatus_d}),
		.wr_en_i(mstatus_en),
		.rd_data_o(mstatus_q),
		.rd_error_o(mstatus_err)
	);
	ibex_csr #(
		.Width(32),
		.ShadowCopy(1'b0),
		.ResetValue(1'sb0)
	) u_mepc_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i(mepc_d),
		.wr_en_i(mepc_en),
		.rd_data_o(mepc_q),
		.rd_error_o()
	);
	assign mie_d[17] = csr_wdata_int[ibex_pkg_CSR_MSIX_BIT];
	assign mie_d[16] = csr_wdata_int[ibex_pkg_CSR_MTIX_BIT];
	assign mie_d[15] = csr_wdata_int[ibex_pkg_CSR_MEIX_BIT];
	assign mie_d[14-:15] = csr_wdata_int[ibex_pkg_CSR_MFIX_BIT_HIGH:ibex_pkg_CSR_MFIX_BIT_LOW];
	ibex_csr #(
		.Width(18),
		.ShadowCopy(1'b0),
		.ResetValue(1'sb0)
	) u_mie_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i({mie_d}),
		.wr_en_i(mie_en),
		.rd_data_o(mie_q),
		.rd_error_o()
	);
	ibex_csr #(
		.Width(32),
		.ShadowCopy(1'b0),
		.ResetValue(1'sb0)
	) u_mscratch_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i(csr_wdata_int),
		.wr_en_i(mscratch_en),
		.rd_data_o(mscratch_q),
		.rd_error_o()
	);
	ibex_csr #(
		.Width(7),
		.ShadowCopy(1'b0),
		.ResetValue(1'sb0)
	) u_mcause_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i({mcause_d}),
		.wr_en_i(mcause_en),
		.rd_data_o(mcause_q),
		.rd_error_o()
	);
	ibex_csr #(
		.Width(32),
		.ShadowCopy(1'b0),
		.ResetValue(1'sb0)
	) u_mtval_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i(mtval_d),
		.wr_en_i(mtval_en),
		.rd_data_o(mtval_q),
		.rd_error_o()
	);
	ibex_csr #(
		.Width(32),
		.ShadowCopy(ShadowCSR),
		.ResetValue(32'd1)
	) u_mtvec_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i(mtvec_d),
		.wr_en_i(mtvec_en),
		.rd_data_o(mtvec_q),
		.rd_error_o(mtvec_err)
	);
	localparam [31:0] DCSR_RESET_VAL = 32'h40000003;
	ibex_csr #(
		.Width(32),
		.ShadowCopy(1'b0),
		.ResetValue({DCSR_RESET_VAL})
	) u_dcsr_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i({dcsr_d}),
		.wr_en_i(dcsr_en),
		.rd_data_o(dcsr_q),
		.rd_error_o()
	);
	ibex_csr #(
		.Width(32),
		.ShadowCopy(1'b0),
		.ResetValue(1'sb0)
	) u_depc_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i(depc_d),
		.wr_en_i(depc_en),
		.rd_data_o(depc_q),
		.rd_error_o()
	);
	ibex_csr #(
		.Width(32),
		.ShadowCopy(1'b0),
		.ResetValue(1'sb0)
	) u_dscratch0_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i(csr_wdata_int),
		.wr_en_i(dscratch0_en),
		.rd_data_o(dscratch0_q),
		.rd_error_o()
	);
	ibex_csr #(
		.Width(32),
		.ShadowCopy(1'b0),
		.ResetValue(1'sb0)
	) u_dscratch1_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i(csr_wdata_int),
		.wr_en_i(dscratch1_en),
		.rd_data_o(dscratch1_q),
		.rd_error_o()
	);
	localparam [2:0] MSTACK_RESET_VAL = 3'b100;
	ibex_csr #(
		.Width(3),
		.ShadowCopy(1'b0),
		.ResetValue({MSTACK_RESET_VAL})
	) u_mstack_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i({mstack_d}),
		.wr_en_i(mstack_en),
		.rd_data_o(mstack_q),
		.rd_error_o()
	);
	ibex_csr #(
		.Width(32),
		.ShadowCopy(1'b0),
		.ResetValue(1'sb0)
	) u_mstack_epc_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i(mstack_epc_d),
		.wr_en_i(mstack_en),
		.rd_data_o(mstack_epc_q),
		.rd_error_o()
	);
	ibex_csr #(
		.Width(7),
		.ShadowCopy(1'b0),
		.ResetValue(1'sb0)
	) u_mstack_cause_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i(mstack_cause_d),
		.wr_en_i(mstack_en),
		.rd_data_o(mstack_cause_q),
		.rd_error_o()
	);
	localparam [11:0] ibex_pkg_CSR_OFF_PMP_ADDR = 12'h3b0;
	localparam [11:0] ibex_pkg_CSR_OFF_PMP_CFG = 12'h3a0;
	generate
		if (PMPEnable) begin : g_pmp_registers
			localparam [95:0] pmp_cfg_rst = 96'b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
			localparam [543:0] pmp_addr_rst = 544'h0;
			localparam [2:0] pmp_mseccfg_rst = 3'b000;
			wire [2:0] pmp_mseccfg_q;
			wire [2:0] pmp_mseccfg_d;
			wire pmp_mseccfg_we;
			wire pmp_mseccfg_err;
			wire [5:0] pmp_cfg [0:PMPNumRegions - 1];
			wire [PMPNumRegions - 1:0] pmp_cfg_locked;
			wire [PMPNumRegions - 1:0] pmp_cfg_wr_suppress;
			reg [5:0] pmp_cfg_wdata [0:PMPNumRegions - 1];
			wire [PMPAddrWidth - 1:0] pmp_addr [0:PMPNumRegions - 1];
			wire [PMPNumRegions - 1:0] pmp_cfg_we;
			wire [PMPNumRegions - 1:0] pmp_cfg_err;
			wire [PMPNumRegions - 1:0] pmp_addr_we;
			wire [PMPNumRegions - 1:0] pmp_addr_err;
			wire any_pmp_entry_locked;
			genvar i;
			for (i = 0; i < ibex_pkg_PMP_MAX_REGIONS; i = i + 1) begin : g_exp_rd_data
				if (i < PMPNumRegions) begin : g_implemented_regions
					assign pmp_cfg_rdata[i] = {pmp_cfg[i][5], 2'b00, pmp_cfg[i][4-:2], pmp_cfg[i][2], pmp_cfg[i][1], pmp_cfg[i][0]};
					if (PMPGranularity == 0) begin : g_pmp_g0
						wire [32:1] sv2v_tmp_646D9;
						assign sv2v_tmp_646D9 = pmp_addr[i];
						always @(*) pmp_addr_rdata[i] = sv2v_tmp_646D9;
					end
					else if (PMPGranularity == 1) begin : g_pmp_g1
						always @(*) begin
							pmp_addr_rdata[i] = pmp_addr[i];
							if ((pmp_cfg[i][4-:2] == 2'b00) || (pmp_cfg[i][4-:2] == 2'b01))
								pmp_addr_rdata[i][PMPGranularity - 1:0] = 1'sb0;
						end
					end
					else begin : g_pmp_g2
						always @(*) begin
							pmp_addr_rdata[i] = {pmp_addr[i], {PMPGranularity - 1 {1'b1}}};
							if ((pmp_cfg[i][4-:2] == 2'b00) || (pmp_cfg[i][4-:2] == 2'b01))
								pmp_addr_rdata[i][PMPGranularity - 1:0] = 1'sb0;
						end
					end
				end
				else begin : g_other_regions
					assign pmp_cfg_rdata[i] = 1'sb0;
					wire [32:1] sv2v_tmp_96282;
					assign sv2v_tmp_96282 = 1'sb0;
					always @(*) pmp_addr_rdata[i] = sv2v_tmp_96282;
				end
			end
			for (i = 0; i < PMPNumRegions; i = i + 1) begin : g_pmp_csrs
				assign pmp_cfg_we[i] = ((csr_we_int & ~pmp_cfg_locked[i]) & ~pmp_cfg_wr_suppress[i]) & (csr_addr == (ibex_pkg_CSR_OFF_PMP_CFG + (i[11:0] >> 2)));
				wire [1:1] sv2v_tmp_43D04;
				assign sv2v_tmp_43D04 = csr_wdata_int[((i % 4) * ibex_pkg_PMP_CFG_W) + 7];
				always @(*) pmp_cfg_wdata[i][5] = sv2v_tmp_43D04;
				always @(*)
					case (csr_wdata_int[((i % 4) * ibex_pkg_PMP_CFG_W) + 3+:2])
						2'b00: pmp_cfg_wdata[i][4-:2] = 2'b00;
						2'b01: pmp_cfg_wdata[i][4-:2] = 2'b01;
						2'b10: pmp_cfg_wdata[i][4-:2] = (PMPGranularity == 0 ? 2'b10 : 2'b00);
						2'b11: pmp_cfg_wdata[i][4-:2] = 2'b11;
						default: pmp_cfg_wdata[i][4-:2] = 2'b00;
					endcase
				wire [1:1] sv2v_tmp_B5F8A;
				assign sv2v_tmp_B5F8A = csr_wdata_int[((i % 4) * ibex_pkg_PMP_CFG_W) + 2];
				always @(*) pmp_cfg_wdata[i][2] = sv2v_tmp_B5F8A;
				wire [1:1] sv2v_tmp_DA81D;
				assign sv2v_tmp_DA81D = (pmp_mseccfg_q[0] ? csr_wdata_int[((i % 4) * ibex_pkg_PMP_CFG_W) + 1] : &csr_wdata_int[(i % 4) * ibex_pkg_PMP_CFG_W+:2]);
				always @(*) pmp_cfg_wdata[i][1] = sv2v_tmp_DA81D;
				wire [1:1] sv2v_tmp_92290;
				assign sv2v_tmp_92290 = csr_wdata_int[(i % 4) * ibex_pkg_PMP_CFG_W];
				always @(*) pmp_cfg_wdata[i][0] = sv2v_tmp_92290;
				ibex_csr #(
					.Width(6),
					.ShadowCopy(ShadowCSR),
					.ResetValue(pmp_cfg_rst[(15 - i) * 6+:6])
				) u_pmp_cfg_csr(
					.clk_i(clk_i),
					.rst_ni(rst_ni),
					.wr_data_i({pmp_cfg_wdata[i]}),
					.wr_en_i(pmp_cfg_we[i]),
					.rd_data_o(pmp_cfg[i]),
					.rd_error_o(pmp_cfg_err[i])
				);
				assign pmp_cfg_locked[i] = pmp_cfg[i][5] & ~pmp_mseccfg_q[2];
				assign pmp_cfg_wr_suppress[i] = (pmp_mseccfg_q[0] & ~pmp_mseccfg[2]) & is_mml_m_exec_cfg(pmp_cfg_wdata[i]);
				if (i < (PMPNumRegions - 1)) begin : g_lower
					assign pmp_addr_we[i] = ((csr_we_int & ~pmp_cfg_locked[i]) & (~pmp_cfg_locked[i + 1] | (pmp_cfg[i + 1][4-:2] != 2'b01))) & (csr_addr == (ibex_pkg_CSR_OFF_PMP_ADDR + i[11:0]));
				end
				else begin : g_upper
					assign pmp_addr_we[i] = (csr_we_int & ~pmp_cfg_locked[i]) & (csr_addr == (ibex_pkg_CSR_OFF_PMP_ADDR + i[11:0]));
				end
				ibex_csr #(
					.Width(PMPAddrWidth),
					.ShadowCopy(ShadowCSR),
					.ResetValue(pmp_addr_rst[((15 - i) * 34) + 33-:PMPAddrWidth])
				) u_pmp_addr_csr(
					.clk_i(clk_i),
					.rst_ni(rst_ni),
					.wr_data_i(csr_wdata_int[31-:PMPAddrWidth]),
					.wr_en_i(pmp_addr_we[i]),
					.rd_data_o(pmp_addr[i]),
					.rd_error_o(pmp_addr_err[i])
				);
				assign csr_pmp_cfg_o[((PMPNumRegions - 1) - i) * 6+:6] = pmp_cfg[i];
				assign csr_pmp_addr_o[((PMPNumRegions - 1) - i) * 34+:34] = {pmp_addr_rdata[i], 2'b00};
			end
			assign pmp_mseccfg_we = csr_we_int & (csr_addr == 12'h747);
			assign pmp_mseccfg_d[0] = (pmp_mseccfg_q[0] ? 1'b1 : csr_wdata_int[ibex_pkg_CSR_MSECCFG_MML_BIT]);
			assign pmp_mseccfg_d[1] = (pmp_mseccfg_q[1] ? 1'b1 : csr_wdata_int[ibex_pkg_CSR_MSECCFG_MMWP_BIT]);
			assign any_pmp_entry_locked = |pmp_cfg_locked;
			assign pmp_mseccfg_d[2] = (any_pmp_entry_locked ? 1'b0 : csr_wdata_int[ibex_pkg_CSR_MSECCFG_RLB_BIT]);
			ibex_csr #(
				.Width(3),
				.ShadowCopy(ShadowCSR),
				.ResetValue(pmp_mseccfg_rst)
			) u_pmp_mseccfg(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.wr_data_i(pmp_mseccfg_d),
				.wr_en_i(pmp_mseccfg_we),
				.rd_data_o(pmp_mseccfg_q),
				.rd_error_o(pmp_mseccfg_err)
			);
			assign pmp_csr_err = (|pmp_cfg_err | |pmp_addr_err) | pmp_mseccfg_err;
			assign pmp_mseccfg = pmp_mseccfg_q;
		end
		else begin : g_no_pmp_tieoffs
			genvar i;
			for (i = 0; i < ibex_pkg_PMP_MAX_REGIONS; i = i + 1) begin : g_rdata
				wire [32:1] sv2v_tmp_96282;
				assign sv2v_tmp_96282 = 1'sb0;
				always @(*) pmp_addr_rdata[i] = sv2v_tmp_96282;
				assign pmp_cfg_rdata[i] = 1'sb0;
			end
			for (i = 0; i < PMPNumRegions; i = i + 1) begin : g_outputs
				assign csr_pmp_cfg_o[((PMPNumRegions - 1) - i) * 6+:6] = 6'b000000;
				assign csr_pmp_addr_o[((PMPNumRegions - 1) - i) * 34+:34] = 1'sb0;
			end
			assign pmp_csr_err = 1'b0;
			assign pmp_mseccfg = 1'sb0;
		end
	endgenerate
	assign csr_pmp_mseccfg_o = pmp_mseccfg;
	always @(*) begin : mcountinhibit_update
		if (mcountinhibit_we == 1'b1)
			mcountinhibit_d = {csr_wdata_int[MHPMCounterNum + 2:2], 1'b0, csr_wdata_int[0]};
		else
			mcountinhibit_d = mcountinhibit_q;
	end
	always @(*) begin : gen_mhpmcounter_incr
		begin : sv2v_autoblock_1
			reg [31:0] i;
			for (i = 0; i < 32; i = i + 1)
				begin : gen_mhpmcounter_incr_inactive
					mhpmcounter_incr[i] = 1'b0;
				end
		end
		mhpmcounter_incr[0] = 1'b1;
		mhpmcounter_incr[1] = 1'b0;
		mhpmcounter_incr[2] = instr_ret_i;
		mhpmcounter_incr[3] = dside_wait_i;
		mhpmcounter_incr[4] = iside_wait_i;
		mhpmcounter_incr[5] = mem_load_i;
		mhpmcounter_incr[6] = mem_store_i;
		mhpmcounter_incr[7] = jump_i;
		mhpmcounter_incr[8] = branch_i;
		mhpmcounter_incr[9] = branch_taken_i;
		mhpmcounter_incr[10] = instr_ret_compressed_i;
		mhpmcounter_incr[11] = mul_wait_i;
		mhpmcounter_incr[12] = div_wait_i;
	end
	always @(*) begin : gen_mhpmevent
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < 32; i = i + 1)
				begin : gen_mhpmevent_active
					mhpmevent[i] = 1'sb0;
					if (i >= 3)
						mhpmevent[i][i - 3] = 1'b1;
				end
		end
		mhpmevent[1] = 1'sb0;
		begin : sv2v_autoblock_3
			reg [31:0] i;
			for (i = 3 + MHPMCounterNum; i < 32; i = i + 1)
				begin : gen_mhpmevent_inactive
					mhpmevent[i] = 1'sb0;
				end
		end
	end
	ibex_counter #(.CounterWidth(64)) mcycle_counter_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.counter_inc_i(mhpmcounter_incr[0] & ~mcountinhibit[0]),
		.counterh_we_i(mhpmcounterh_we[0]),
		.counter_we_i(mhpmcounter_we[0]),
		.counter_val_i(csr_wdata_int),
		.counter_val_o(mhpmcounter[0]),
		.counter_val_upd_o()
	);
	ibex_counter #(
		.CounterWidth(64),
		.ProvideValUpd(1)
	) minstret_counter_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.counter_inc_i(mhpmcounter_incr[2] & ~mcountinhibit[2]),
		.counterh_we_i(mhpmcounterh_we[2]),
		.counter_we_i(mhpmcounter_we[2]),
		.counter_val_i(csr_wdata_int),
		.counter_val_o(minstret_raw),
		.counter_val_upd_o(minstret_next)
	);
	assign mhpmcounter[2] = (instr_ret_spec_i & ~mcountinhibit[2] ? minstret_next : minstret_raw);
	assign mhpmcounter[1] = 1'sb0;
	assign unused_mhpmcounter_we_1 = mhpmcounter_we[1];
	assign unused_mhpmcounterh_we_1 = mhpmcounterh_we[1];
	assign unused_mhpmcounter_incr_1 = mhpmcounter_incr[1];
	genvar i;
	generate
		for (i = 0; i < 29; i = i + 1) begin : gen_cntrs
			localparam signed [31:0] Cnt = i + 3;
			if (i < MHPMCounterNum) begin : gen_imp
				wire [63:0] mhpmcounter_raw;
				wire [63:0] mhpmcounter_next;
				ibex_counter #(
					.CounterWidth(MHPMCounterWidth),
					.ProvideValUpd(Cnt == 10)
				) mcounters_variable_i(
					.clk_i(clk_i),
					.rst_ni(rst_ni),
					.counter_inc_i(mhpmcounter_incr[Cnt] & ~mcountinhibit[Cnt]),
					.counterh_we_i(mhpmcounterh_we[Cnt]),
					.counter_we_i(mhpmcounter_we[Cnt]),
					.counter_val_i(csr_wdata_int),
					.counter_val_o(mhpmcounter_raw),
					.counter_val_upd_o(mhpmcounter_next)
				);
				if (Cnt == 10) begin : gen_compressed_instr_cnt
					assign mhpmcounter[Cnt] = (instr_ret_compressed_spec_i & ~mcountinhibit[Cnt] ? mhpmcounter_next : mhpmcounter_raw);
				end
				else begin : gen_other_cnts
					wire [63:0] unused_mhpmcounter_next;
					assign mhpmcounter[Cnt] = mhpmcounter_raw;
					assign unused_mhpmcounter_next = mhpmcounter_next;
				end
			end
			else begin : gen_unimp
				assign mhpmcounter[Cnt] = 1'sb0;
				if (Cnt == 10) begin : gen_no_compressed_instr_cnt
					wire unused_instr_ret_compressed_spec_i;
					assign unused_instr_ret_compressed_spec_i = instr_ret_compressed_spec_i;
				end
			end
		end
		if (MHPMCounterNum < 29) begin : g_mcountinhibit_reduced
			wire [(29 - MHPMCounterNum) - 1:0] unused_mhphcounter_we;
			wire [(29 - MHPMCounterNum) - 1:0] unused_mhphcounterh_we;
			wire [(29 - MHPMCounterNum) - 1:0] unused_mhphcounter_incr;
			assign mcountinhibit = {{29 - MHPMCounterNum {1'b0}}, mcountinhibit_q};
			assign unused_mhphcounter_we = mhpmcounter_we[31:MHPMCounterNum + 3];
			assign unused_mhphcounterh_we = mhpmcounterh_we[31:MHPMCounterNum + 3];
			assign unused_mhphcounter_incr = mhpmcounter_incr[31:MHPMCounterNum + 3];
		end
		else begin : g_mcountinhibit_full
			assign mcountinhibit = mcountinhibit_q;
		end
	endgenerate
	always @(posedge clk_i)
		if (!rst_ni)
			mcountinhibit_q <= 1'sb0;
		else
			mcountinhibit_q <= mcountinhibit_d;
	generate
		if (DbgTriggerEn) begin : gen_trigger_regs
			localparam [31:0] DbgHwNumLen = (DbgHwBreakNum > 1 ? $clog2(DbgHwBreakNum) : 1);
			localparam [31:0] MaxTselect = DbgHwBreakNum - 1;
			wire [DbgHwNumLen - 1:0] tselect_d;
			wire [DbgHwNumLen - 1:0] tselect_q;
			wire tmatch_control_d;
			wire [DbgHwBreakNum - 1:0] tmatch_control_q;
			wire [31:0] tmatch_value_d;
			wire [31:0] tmatch_value_q [0:DbgHwBreakNum - 1];
			wire selected_tmatch_control;
			wire [31:0] selected_tmatch_value;
			wire tselect_we;
			wire [DbgHwBreakNum - 1:0] tmatch_control_we;
			wire [DbgHwBreakNum - 1:0] tmatch_value_we;
			wire [DbgHwBreakNum - 1:0] trigger_match;
			assign tselect_we = (csr_we_int & debug_mode_i) & (csr_addr_i == 12'h7a0);
			genvar i;
			for (i = 0; i < DbgHwBreakNum; i = i + 1) begin : g_dbg_tmatch_we
				assign tmatch_control_we[i] = (((i[DbgHwNumLen - 1:0] == tselect_q) & csr_we_int) & debug_mode_i) & (csr_addr_i == 12'h7a1);
				assign tmatch_value_we[i] = (((i[DbgHwNumLen - 1:0] == tselect_q) & csr_we_int) & debug_mode_i) & (csr_addr_i == 12'h7a2);
			end
			assign tselect_d = (csr_wdata_int < DbgHwBreakNum ? csr_wdata_int[DbgHwNumLen - 1:0] : MaxTselect[DbgHwNumLen - 1:0]);
			assign tmatch_control_d = csr_wdata_int[2];
			assign tmatch_value_d = csr_wdata_int[31:0];
			ibex_csr #(
				.Width(DbgHwNumLen),
				.ShadowCopy(1'b0),
				.ResetValue(1'sb0)
			) u_tselect_csr(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.wr_data_i(tselect_d),
				.wr_en_i(tselect_we),
				.rd_data_o(tselect_q),
				.rd_error_o()
			);
			for (i = 0; i < DbgHwBreakNum; i = i + 1) begin : g_dbg_tmatch_reg
				ibex_csr #(
					.Width(1),
					.ShadowCopy(1'b0),
					.ResetValue(1'sb0)
				) u_tmatch_control_csr(
					.clk_i(clk_i),
					.rst_ni(rst_ni),
					.wr_data_i(tmatch_control_d),
					.wr_en_i(tmatch_control_we[i]),
					.rd_data_o(tmatch_control_q[i]),
					.rd_error_o()
				);
				ibex_csr #(
					.Width(32),
					.ShadowCopy(1'b0),
					.ResetValue(1'sb0)
				) u_tmatch_value_csr(
					.clk_i(clk_i),
					.rst_ni(rst_ni),
					.wr_data_i(tmatch_value_d),
					.wr_en_i(tmatch_value_we[i]),
					.rd_data_o(tmatch_value_q[i]),
					.rd_error_o()
				);
			end
			localparam [31:0] TSelectRdataPadlen = (DbgHwNumLen >= 32 ? 0 : 32 - DbgHwNumLen);
			assign tselect_rdata = {{TSelectRdataPadlen {1'b0}}, tselect_q};
			if (DbgHwBreakNum > 1) begin : g_dbg_tmatch_multiple_select
				assign selected_tmatch_control = tmatch_control_q[tselect_q];
				assign selected_tmatch_value = tmatch_value_q[tselect_q];
			end
			else begin : g_dbg_tmatch_single_select
				assign selected_tmatch_control = tmatch_control_q[0];
				assign selected_tmatch_value = tmatch_value_q[0];
			end
			assign tmatch_control_rdata = {29'h05000209, selected_tmatch_control, 2'b00};
			assign tmatch_value_rdata = selected_tmatch_value;
			for (i = 0; i < DbgHwBreakNum; i = i + 1) begin : g_dbg_trigger_match
				assign trigger_match[i] = tmatch_control_q[i] & (pc_if_i[31:0] == tmatch_value_q[i]);
			end
			assign trigger_match_o = |trigger_match;
		end
		else begin : gen_no_trigger_regs
			assign tselect_rdata = 'b0;
			assign tmatch_control_rdata = 'b0;
			assign tmatch_value_rdata = 'b0;
			assign trigger_match_o = 'b0;
		end
	endgenerate
	assign cpuctrlsts_part_wdata_raw = csr_wdata_int[7:0];
	generate
		if (DataIndTiming) begin : gen_dit
			assign cpuctrlsts_part_wdata[1] = cpuctrlsts_part_wdata_raw[1];
		end
		else begin : gen_no_dit
			wire unused_dit;
			assign unused_dit = cpuctrlsts_part_wdata_raw[1];
			assign cpuctrlsts_part_wdata[1] = 1'b0;
		end
	endgenerate
	assign data_ind_timing_o = cpuctrlsts_part_q[1];
	generate
		if (DummyInstructions) begin : gen_dummy
			assign cpuctrlsts_part_wdata[2] = cpuctrlsts_part_wdata_raw[2];
			assign cpuctrlsts_part_wdata[5-:3] = cpuctrlsts_part_wdata_raw[5-:3];
			assign dummy_instr_seed_en_o = csr_we_int && (csr_addr == 12'h7c1);
			assign dummy_instr_seed_o = csr_wdata_int;
		end
		else begin : gen_no_dummy
			wire unused_dummy_en;
			wire [2:0] unused_dummy_mask;
			assign unused_dummy_en = cpuctrlsts_part_wdata_raw[2];
			assign unused_dummy_mask = cpuctrlsts_part_wdata_raw[5-:3];
			assign cpuctrlsts_part_wdata[2] = 1'b0;
			assign cpuctrlsts_part_wdata[5-:3] = 3'b000;
			assign dummy_instr_seed_en_o = 1'b0;
			assign dummy_instr_seed_o = 1'sb0;
		end
	endgenerate
	assign dummy_instr_en_o = cpuctrlsts_part_q[2];
	assign dummy_instr_mask_o = cpuctrlsts_part_q[5-:3];
	generate
		if (ICache) begin : gen_icache_enable
			assign cpuctrlsts_part_wdata[0] = cpuctrlsts_part_wdata_raw[0];
			ibex_csr #(
				.Width(1),
				.ShadowCopy(ShadowCSR),
				.ResetValue(1'b0)
			) u_cpuctrlsts_ic_scr_key_valid_q_csr(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.wr_data_i(ic_scr_key_valid_i),
				.wr_en_i(1'b1),
				.rd_data_o(cpuctrlsts_ic_scr_key_valid_q),
				.rd_error_o(cpuctrlsts_ic_scr_key_err)
			);
		end
		else begin : gen_no_icache
			wire unused_icen;
			assign unused_icen = cpuctrlsts_part_wdata_raw[0];
			assign cpuctrlsts_part_wdata[0] = 1'b0;
			wire unused_ic_scr_key_valid;
			assign unused_ic_scr_key_valid = ic_scr_key_valid_i;
			assign cpuctrlsts_ic_scr_key_valid_q = 1'b0;
			assign cpuctrlsts_ic_scr_key_err = 1'b0;
		end
	endgenerate
	assign cpuctrlsts_part_wdata[7] = cpuctrlsts_part_wdata_raw[7];
	assign cpuctrlsts_part_wdata[6] = cpuctrlsts_part_wdata_raw[6];
	assign icache_enable_o = cpuctrlsts_part_q[0] & ~(debug_mode_i | debug_mode_entering_i);
	ibex_csr #(
		.Width(8),
		.ShadowCopy(ShadowCSR),
		.ResetValue(1'sb0)
	) u_cpuctrlsts_part_csr(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.wr_data_i({cpuctrlsts_part_d}),
		.wr_en_i(cpuctrlsts_part_we),
		.rd_data_o(cpuctrlsts_part_q),
		.rd_error_o(cpuctrlsts_part_err)
	);
	assign csr_shadow_err_o = (((mstatus_err | mtvec_err) | pmp_csr_err) | cpuctrlsts_part_err) | cpuctrlsts_ic_scr_key_err;
endmodule
module ibex_prefetch_buffer (
	clk_i,
	rst_ni,
	req_i,
	branch_i,
	addr_i,
	ready_i,
	valid_o,
	rdata_o,
	addr_o,
	err_o,
	err_plus2_o,
	instr_req_o,
	instr_gnt_i,
	instr_addr_o,
	instr_rdata_i,
	instr_err_i,
	instr_rvalid_i,
	busy_o
);
	parameter [0:0] ResetAll = 1'b0;
	input wire clk_i;
	input wire rst_ni;
	input wire req_i;
	input wire branch_i;
	input wire [31:0] addr_i;
	input wire ready_i;
	output wire valid_o;
	output wire [31:0] rdata_o;
	output wire [31:0] addr_o;
	output wire err_o;
	output wire err_plus2_o;
	output wire instr_req_o;
	input wire instr_gnt_i;
	output wire [31:0] instr_addr_o;
	input wire [31:0] instr_rdata_i;
	input wire instr_err_i;
	input wire instr_rvalid_i;
	output wire busy_o;
	localparam [31:0] NUM_REQS = 2;
	wire valid_new_req;
	wire valid_req;
	wire valid_req_d;
	reg valid_req_q;
	wire discard_req_d;
	reg discard_req_q;
	wire [1:0] rdata_outstanding_n;
	wire [1:0] rdata_outstanding_s;
	reg [1:0] rdata_outstanding_q;
	wire [1:0] branch_discard_n;
	wire [1:0] branch_discard_s;
	reg [1:0] branch_discard_q;
	wire [1:0] rdata_outstanding_rev;
	wire [31:0] stored_addr_d;
	reg [31:0] stored_addr_q;
	wire stored_addr_en;
	wire [31:0] fetch_addr_d;
	reg [31:0] fetch_addr_q;
	wire fetch_addr_en;
	wire [31:0] instr_addr;
	wire [31:0] instr_addr_w_aligned;
	wire fifo_valid;
	wire [31:0] fifo_addr;
	wire fifo_ready;
	wire fifo_clear;
	wire [1:0] fifo_busy;
	assign busy_o = |rdata_outstanding_q | instr_req_o;
	assign fifo_clear = branch_i;
	genvar i;
	generate
		for (i = 0; i < NUM_REQS; i = i + 1) begin : gen_rd_rev
			assign rdata_outstanding_rev[i] = rdata_outstanding_q[1 - i];
		end
	endgenerate
	assign fifo_ready = ~&(fifo_busy | rdata_outstanding_rev);
	ibex_fetch_fifo #(
		.NUM_REQS(NUM_REQS),
		.ResetAll(ResetAll)
	) fifo_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.clear_i(fifo_clear),
		.busy_o(fifo_busy),
		.in_valid_i(fifo_valid),
		.in_addr_i(fifo_addr),
		.in_rdata_i(instr_rdata_i),
		.in_err_i(instr_err_i),
		.out_valid_o(valid_o),
		.out_ready_i(ready_i),
		.out_rdata_o(rdata_o),
		.out_addr_o(addr_o),
		.out_err_o(err_o),
		.out_err_plus2_o(err_plus2_o)
	);
	assign valid_new_req = (req_i & (fifo_ready | branch_i)) & ~rdata_outstanding_q[1];
	assign valid_req = valid_req_q | valid_new_req;
	assign valid_req_d = valid_req & ~instr_gnt_i;
	assign discard_req_d = valid_req_q & (branch_i | discard_req_q);
	assign stored_addr_en = (valid_new_req & ~valid_req_q) & ~instr_gnt_i;
	assign stored_addr_d = instr_addr;
	generate
		if (ResetAll) begin : g_stored_addr_ra
			always @(posedge clk_i)
				if (!rst_ni)
					stored_addr_q <= 1'sb0;
				else if (stored_addr_en)
					stored_addr_q <= stored_addr_d;
		end
		else begin : g_stored_addr_nr
			always @(posedge clk_i)
				if (stored_addr_en)
					stored_addr_q <= stored_addr_d;
		end
	endgenerate
	assign fetch_addr_en = branch_i | (valid_new_req & ~valid_req_q);
	assign fetch_addr_d = (branch_i ? addr_i : {fetch_addr_q[31:2], 2'b00}) + {{29 {1'b0}}, valid_new_req & ~valid_req_q, 2'b00};
	generate
		if (ResetAll) begin : g_fetch_addr_ra
			always @(posedge clk_i)
				if (!rst_ni)
					fetch_addr_q <= 1'sb0;
				else if (fetch_addr_en)
					fetch_addr_q <= fetch_addr_d;
		end
		else begin : g_fetch_addr_nr
			always @(posedge clk_i)
				if (fetch_addr_en)
					fetch_addr_q <= fetch_addr_d;
		end
	endgenerate
	assign instr_addr = (valid_req_q ? stored_addr_q : (branch_i ? addr_i : fetch_addr_q));
	assign instr_addr_w_aligned = {instr_addr[31:2], 2'b00};
	generate
		for (i = 0; i < NUM_REQS; i = i + 1) begin : g_outstanding_reqs
			if (i == 0) begin : g_req0
				assign rdata_outstanding_n[i] = (valid_req & instr_gnt_i) | rdata_outstanding_q[i];
				assign branch_discard_n[i] = (((valid_req & instr_gnt_i) & discard_req_d) | (branch_i & rdata_outstanding_q[i])) | branch_discard_q[i];
			end
			else begin : g_reqtop
				assign rdata_outstanding_n[i] = ((valid_req & instr_gnt_i) & rdata_outstanding_q[i - 1]) | rdata_outstanding_q[i];
				assign branch_discard_n[i] = ((((valid_req & instr_gnt_i) & discard_req_d) & rdata_outstanding_q[i - 1]) | (branch_i & rdata_outstanding_q[i])) | branch_discard_q[i];
			end
		end
	endgenerate
	assign rdata_outstanding_s = (instr_rvalid_i ? {1'b0, rdata_outstanding_n[1:1]} : rdata_outstanding_n);
	assign branch_discard_s = (instr_rvalid_i ? {1'b0, branch_discard_n[1:1]} : branch_discard_n);
	assign fifo_valid = instr_rvalid_i & ~branch_discard_q[0];
	assign fifo_addr = addr_i;
	always @(posedge clk_i)
		if (!rst_ni) begin
			valid_req_q <= 1'b0;
			discard_req_q <= 1'b0;
			rdata_outstanding_q <= 'b0;
			branch_discard_q <= 'b0;
		end
		else begin
			valid_req_q <= valid_req_d;
			discard_req_q <= discard_req_d;
			rdata_outstanding_q <= rdata_outstanding_s;
			branch_discard_q <= branch_discard_s;
		end
	assign instr_req_o = valid_req;
	assign instr_addr_o = instr_addr_w_aligned;
endmodule
module ibex_icache (
	clk_i,
	rst_ni,
	req_i,
	branch_i,
	addr_i,
	ready_i,
	valid_o,
	rdata_o,
	addr_o,
	err_o,
	err_plus2_o,
	instr_req_o,
	instr_gnt_i,
	instr_addr_o,
	instr_rdata_i,
	instr_err_i,
	instr_rvalid_i,
	ic_tag_req_o,
	ic_tag_write_o,
	ic_tag_addr_o,
	ic_tag_wdata_o,
	ic_tag_rdata_i,
	ic_data_req_o,
	ic_data_write_o,
	ic_data_addr_o,
	ic_data_wdata_o,
	ic_data_rdata_i,
	ic_scr_key_valid_i,
	ic_scr_key_req_o,
	icache_enable_i,
	icache_inval_i,
	busy_o,
	ecc_error_o
);
	parameter [0:0] ICacheECC = 1'b0;
	parameter [0:0] ResetAll = 1'b0;
	localparam [31:0] ibex_pkg_BUS_SIZE = 32;
	parameter [31:0] BusSizeECC = ibex_pkg_BUS_SIZE;
	localparam [31:0] ibex_pkg_ADDR_W = 32;
	localparam [31:0] ibex_pkg_IC_LINE_SIZE = 64;
	localparam [31:0] ibex_pkg_IC_LINE_BYTES = 8;
	localparam [31:0] ibex_pkg_IC_NUM_WAYS = 2;
	localparam [31:0] ibex_pkg_IC_SIZE_BYTES = 4096;
	localparam [31:0] ibex_pkg_IC_NUM_LINES = (ibex_pkg_IC_SIZE_BYTES / ibex_pkg_IC_NUM_WAYS) / ibex_pkg_IC_LINE_BYTES;
	localparam [31:0] ibex_pkg_IC_INDEX_W = $clog2(ibex_pkg_IC_NUM_LINES);
	localparam [31:0] ibex_pkg_IC_LINE_W = 3;
	localparam [31:0] ibex_pkg_IC_TAG_SIZE = ((ibex_pkg_ADDR_W - ibex_pkg_IC_INDEX_W) - ibex_pkg_IC_LINE_W) + 1;
	parameter [31:0] TagSizeECC = ibex_pkg_IC_TAG_SIZE;
	parameter [31:0] LineSizeECC = ibex_pkg_IC_LINE_SIZE;
	parameter [0:0] BranchCache = 1'b0;
	input wire clk_i;
	input wire rst_ni;
	input wire req_i;
	input wire branch_i;
	input wire [31:0] addr_i;
	input wire ready_i;
	output wire valid_o;
	output wire [31:0] rdata_o;
	output wire [31:0] addr_o;
	output wire err_o;
	output wire err_plus2_o;
	output wire instr_req_o;
	input wire instr_gnt_i;
	output wire [31:0] instr_addr_o;
	input wire [31:0] instr_rdata_i;
	input wire instr_err_i;
	input wire instr_rvalid_i;
	output wire [1:0] ic_tag_req_o;
	output wire ic_tag_write_o;
	output wire [ibex_pkg_IC_INDEX_W - 1:0] ic_tag_addr_o;
	output wire [TagSizeECC - 1:0] ic_tag_wdata_o;
	input wire [(ibex_pkg_IC_NUM_WAYS * TagSizeECC) - 1:0] ic_tag_rdata_i;
	output wire [1:0] ic_data_req_o;
	output wire ic_data_write_o;
	output wire [ibex_pkg_IC_INDEX_W - 1:0] ic_data_addr_o;
	output wire [LineSizeECC - 1:0] ic_data_wdata_o;
	input wire [(ibex_pkg_IC_NUM_WAYS * LineSizeECC) - 1:0] ic_data_rdata_i;
	input wire ic_scr_key_valid_i;
	output reg ic_scr_key_req_o;
	input wire icache_enable_i;
	input wire icache_inval_i;
	output wire busy_o;
	output wire ecc_error_o;
	localparam [31:0] NUM_FB = 4;
	localparam [31:0] FB_THRESHOLD = 2;
	wire [31:0] lookup_addr_aligned;
	wire [31:0] prefetch_addr_d;
	reg [31:0] prefetch_addr_q;
	wire prefetch_addr_en;
	wire lookup_throttle;
	wire lookup_req_ic0;
	wire [31:0] lookup_addr_ic0;
	wire [ibex_pkg_IC_INDEX_W - 1:0] lookup_index_ic0;
	wire fill_req_ic0;
	wire [ibex_pkg_IC_INDEX_W - 1:0] fill_index_ic0;
	wire [ibex_pkg_IC_TAG_SIZE - 1:0] fill_tag_ic0;
	wire [63:0] fill_wdata_ic0;
	wire lookup_grant_ic0;
	wire lookup_actual_ic0;
	wire fill_grant_ic0;
	wire tag_req_ic0;
	wire [ibex_pkg_IC_INDEX_W - 1:0] tag_index_ic0;
	wire [1:0] tag_banks_ic0;
	wire tag_write_ic0;
	wire [TagSizeECC - 1:0] tag_wdata_ic0;
	wire data_req_ic0;
	wire [ibex_pkg_IC_INDEX_W - 1:0] data_index_ic0;
	wire [1:0] data_banks_ic0;
	wire data_write_ic0;
	wire [LineSizeECC - 1:0] data_wdata_ic0;
	wire [(ibex_pkg_IC_NUM_WAYS * TagSizeECC) - 1:0] tag_rdata_ic1;
	wire [(ibex_pkg_IC_NUM_WAYS * LineSizeECC) - 1:0] data_rdata_ic1;
	reg [LineSizeECC - 1:0] hit_data_ecc_ic1;
	wire [63:0] hit_data_ic1;
	reg lookup_valid_ic1;
	localparam [31:0] ibex_pkg_IC_INDEX_HI = (ibex_pkg_IC_INDEX_W + ibex_pkg_IC_LINE_W) - 1;
	reg [31:ibex_pkg_IC_INDEX_HI + 1] lookup_addr_ic1;
	wire [1:0] tag_match_ic1;
	wire tag_hit_ic1;
	wire [1:0] tag_invalid_ic1;
	wire [1:0] lowest_invalid_way_ic1;
	wire [1:0] round_robin_way_ic1;
	reg [1:0] round_robin_way_q;
	wire [1:0] sel_way_ic1;
	wire ecc_err_ic1;
	wire ecc_write_req;
	wire [1:0] ecc_write_ways;
	wire [ibex_pkg_IC_INDEX_W - 1:0] ecc_write_index;
	reg [1:0] fb_fill_level;
	wire fill_cache_new;
	wire fill_new_alloc;
	wire fill_spec_req;
	wire fill_spec_done;
	wire fill_spec_hold;
	wire [(NUM_FB * NUM_FB) - 1:0] fill_older_d;
	reg [(NUM_FB * NUM_FB) - 1:0] fill_older_q;
	wire [3:0] fill_alloc_sel;
	wire [3:0] fill_alloc;
	wire [3:0] fill_busy_d;
	reg [3:0] fill_busy_q;
	wire [3:0] fill_done;
	reg [3:0] fill_in_ic1;
	wire [3:0] fill_stale_d;
	reg [3:0] fill_stale_q;
	wire [3:0] fill_cache_d;
	reg [3:0] fill_cache_q;
	wire [3:0] fill_hit_ic1;
	wire [3:0] fill_hit_d;
	reg [3:0] fill_hit_q;
	localparam [31:0] ibex_pkg_BUS_BYTES = 4;
	localparam [31:0] ibex_pkg_IC_LINE_BEATS = ibex_pkg_IC_LINE_BYTES / ibex_pkg_BUS_BYTES;
	localparam [31:0] ibex_pkg_IC_LINE_BEATS_W = $clog2(ibex_pkg_IC_LINE_BEATS);
	wire [(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (NUM_FB * (ibex_pkg_IC_LINE_BEATS_W + 1)) - 1 : (NUM_FB * (1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W - 1)):(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W + 0)] fill_ext_cnt_d;
	reg [(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (NUM_FB * (ibex_pkg_IC_LINE_BEATS_W + 1)) - 1 : (NUM_FB * (1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W - 1)):(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W + 0)] fill_ext_cnt_q;
	wire [3:0] fill_ext_hold_d;
	reg [3:0] fill_ext_hold_q;
	wire [3:0] fill_ext_done_d;
	reg [3:0] fill_ext_done_q;
	wire [(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (NUM_FB * (ibex_pkg_IC_LINE_BEATS_W + 1)) - 1 : (NUM_FB * (1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W - 1)):(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W + 0)] fill_rvd_cnt_d;
	reg [(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (NUM_FB * (ibex_pkg_IC_LINE_BEATS_W + 1)) - 1 : (NUM_FB * (1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W - 1)):(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W + 0)] fill_rvd_cnt_q;
	wire [3:0] fill_rvd_done;
	wire [3:0] fill_ram_done_d;
	reg [3:0] fill_ram_done_q;
	wire [3:0] fill_out_grant;
	wire [(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (NUM_FB * (ibex_pkg_IC_LINE_BEATS_W + 1)) - 1 : (NUM_FB * (1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W - 1)):(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W + 0)] fill_out_cnt_d;
	reg [(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (NUM_FB * (ibex_pkg_IC_LINE_BEATS_W + 1)) - 1 : (NUM_FB * (1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W - 1)):(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W + 0)] fill_out_cnt_q;
	wire [3:0] fill_out_done;
	wire [3:0] fill_ext_req;
	wire [3:0] fill_rvd_exp;
	wire [3:0] fill_ram_req;
	wire [3:0] fill_out_req;
	wire [3:0] fill_data_sel;
	wire [3:0] fill_data_reg;
	wire [3:0] fill_data_hit;
	wire [3:0] fill_data_rvd;
	wire [(NUM_FB * ibex_pkg_IC_LINE_BEATS_W) - 1:0] fill_ext_off;
	wire [(NUM_FB * ibex_pkg_IC_LINE_BEATS_W) - 1:0] fill_rvd_off;
	wire [(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (NUM_FB * (ibex_pkg_IC_LINE_BEATS_W + 1)) - 1 : (NUM_FB * (1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W - 1)):(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W + 0)] fill_ext_beat;
	wire [(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (NUM_FB * (ibex_pkg_IC_LINE_BEATS_W + 1)) - 1 : (NUM_FB * (1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W - 1)):(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W + 0)] fill_rvd_beat;
	wire [3:0] fill_ext_arb;
	wire [3:0] fill_ram_arb;
	wire [3:0] fill_out_arb;
	wire [3:0] fill_rvd_arb;
	wire [3:0] fill_entry_en;
	wire [3:0] fill_addr_en;
	wire [3:0] fill_way_en;
	wire [(NUM_FB * ibex_pkg_IC_LINE_BEATS) - 1:0] fill_data_en;
	wire [(NUM_FB * ibex_pkg_IC_LINE_BEATS) - 1:0] fill_err_d;
	reg [(NUM_FB * ibex_pkg_IC_LINE_BEATS) - 1:0] fill_err_q;
	reg [31:0] fill_addr_q [0:3];
	reg [1:0] fill_way_q [0:3];
	wire [63:0] fill_data_d [0:3];
	reg [63:0] fill_data_q [0:3];
	localparam [31:0] ibex_pkg_BUS_W = 2;
	reg [31:ibex_pkg_BUS_W] fill_ext_req_addr;
	reg [31:0] fill_ram_req_addr;
	reg [1:0] fill_ram_req_way;
	reg [63:0] fill_ram_req_data;
	reg [63:0] fill_out_data;
	reg [ibex_pkg_IC_LINE_BEATS - 1:0] fill_out_err;
	wire instr_req;
	wire [31:ibex_pkg_BUS_W] instr_addr;
	wire skid_complete_instr;
	wire skid_ready;
	wire output_compressed;
	wire skid_valid_d;
	reg skid_valid_q;
	wire skid_en;
	wire [15:0] skid_data_d;
	reg [15:0] skid_data_q;
	reg skid_err_q;
	wire output_valid;
	wire addr_incr_two;
	wire output_addr_en;
	wire [31:1] output_addr_incr;
	wire [31:1] output_addr_d;
	reg [31:1] output_addr_q;
	reg [15:0] output_data_lo;
	reg [15:0] output_data_hi;
	wire data_valid;
	wire output_ready;
	wire [63:0] line_data;
	wire [ibex_pkg_IC_LINE_BEATS - 1:0] line_err;
	reg [31:0] line_data_muxed;
	reg line_err_muxed;
	wire [31:0] output_data;
	wire output_err;
	reg [1:0] inval_state_q;
	reg [1:0] inval_state_d;
	reg inval_write_req;
	reg inval_block_cache;
	reg [ibex_pkg_IC_INDEX_W - 1:0] inval_index_d;
	reg [ibex_pkg_IC_INDEX_W - 1:0] inval_index_q;
	reg inval_index_en;
	wire inval_active;
	assign lookup_addr_aligned = {lookup_addr_ic0[31:ibex_pkg_IC_LINE_W], {ibex_pkg_IC_LINE_W {1'b0}}};
	assign prefetch_addr_d = (lookup_grant_ic0 ? lookup_addr_aligned + {{(ibex_pkg_ADDR_W - ibex_pkg_IC_LINE_W) - 1 {1'b0}}, 1'b1, {ibex_pkg_IC_LINE_W {1'b0}}} : addr_i);
	assign prefetch_addr_en = branch_i | lookup_grant_ic0;
	generate
		if (ResetAll) begin : g_prefetch_addr_ra
			always @(posedge clk_i)
				if (!rst_ni)
					prefetch_addr_q <= 1'sb0;
				else if (prefetch_addr_en)
					prefetch_addr_q <= prefetch_addr_d;
		end
		else begin : g_prefetch_addr_nr
			always @(posedge clk_i)
				if (prefetch_addr_en)
					prefetch_addr_q <= prefetch_addr_d;
		end
	endgenerate
	assign lookup_throttle = fb_fill_level > FB_THRESHOLD[1:0];
	assign lookup_req_ic0 = ((req_i & ~&fill_busy_q) & (branch_i | ~lookup_throttle)) & ~ecc_write_req;
	assign lookup_addr_ic0 = (branch_i ? addr_i : prefetch_addr_q);
	assign lookup_index_ic0 = lookup_addr_ic0[ibex_pkg_IC_INDEX_HI:ibex_pkg_IC_LINE_W];
	assign fill_req_ic0 = |fill_ram_req;
	assign fill_index_ic0 = fill_ram_req_addr[ibex_pkg_IC_INDEX_HI:ibex_pkg_IC_LINE_W];
	assign fill_tag_ic0 = {~inval_write_req & ~ecc_write_req, fill_ram_req_addr[31:ibex_pkg_IC_INDEX_HI + 1]};
	assign fill_wdata_ic0 = fill_ram_req_data;
	assign lookup_grant_ic0 = lookup_req_ic0;
	assign fill_grant_ic0 = ((fill_req_ic0 & ~lookup_req_ic0) & ~inval_write_req) & ~ecc_write_req;
	assign lookup_actual_ic0 = (lookup_grant_ic0 & icache_enable_i) & ~inval_block_cache;
	assign tag_req_ic0 = ((lookup_req_ic0 | fill_req_ic0) | inval_write_req) | ecc_write_req;
	assign tag_index_ic0 = (inval_write_req ? inval_index_q : (ecc_write_req ? ecc_write_index : (fill_grant_ic0 ? fill_index_ic0 : lookup_index_ic0)));
	assign tag_banks_ic0 = (ecc_write_req ? ecc_write_ways : (fill_grant_ic0 ? fill_ram_req_way : {ibex_pkg_IC_NUM_WAYS {1'b1}}));
	assign tag_write_ic0 = (fill_grant_ic0 | inval_write_req) | ecc_write_req;
	assign data_req_ic0 = lookup_req_ic0 | fill_req_ic0;
	assign data_index_ic0 = tag_index_ic0;
	assign data_banks_ic0 = tag_banks_ic0;
	assign data_write_ic0 = tag_write_ic0;
	generate
		if (ICacheECC) begin : gen_ecc_wdata
			wire [21:0] tag_ecc_input_padded;
			wire [27:0] tag_ecc_output_padded;
			wire [22 - ibex_pkg_IC_TAG_SIZE:0] unused_tag_ecc_output;
			assign tag_ecc_input_padded = {{22 - ibex_pkg_IC_TAG_SIZE {1'b0}}, fill_tag_ic0};
			assign unused_tag_ecc_output = tag_ecc_output_padded[21:ibex_pkg_IC_TAG_SIZE - 1];
			prim_secded_inv_28_22_enc tag_ecc_enc(
				.data_i(tag_ecc_input_padded),
				.data_o(tag_ecc_output_padded)
			);
			assign tag_wdata_ic0 = {tag_ecc_output_padded[27:22], tag_ecc_output_padded[ibex_pkg_IC_TAG_SIZE - 1:0]};
			genvar bank;
			for (bank = 0; bank < ibex_pkg_IC_LINE_BEATS; bank = bank + 1) begin : gen_ecc_banks
				prim_secded_inv_39_32_enc data_ecc_enc(
					.data_i(fill_wdata_ic0[bank * ibex_pkg_BUS_SIZE+:ibex_pkg_BUS_SIZE]),
					.data_o(data_wdata_ic0[bank * BusSizeECC+:BusSizeECC])
				);
			end
		end
		else begin : gen_noecc_wdata
			assign tag_wdata_ic0 = fill_tag_ic0;
			assign data_wdata_ic0 = fill_wdata_ic0;
		end
	endgenerate
	assign ic_tag_req_o = {ibex_pkg_IC_NUM_WAYS {tag_req_ic0}} & tag_banks_ic0;
	assign ic_tag_write_o = tag_write_ic0;
	assign ic_tag_addr_o = tag_index_ic0;
	assign ic_tag_wdata_o = tag_wdata_ic0;
	assign tag_rdata_ic1 = ic_tag_rdata_i;
	assign ic_data_req_o = {ibex_pkg_IC_NUM_WAYS {data_req_ic0}} & data_banks_ic0;
	assign ic_data_write_o = data_write_ic0;
	assign ic_data_addr_o = data_index_ic0;
	assign ic_data_wdata_o = data_wdata_ic0;
	assign data_rdata_ic1 = ic_data_rdata_i;
	always @(posedge clk_i)
		if (!rst_ni)
			lookup_valid_ic1 <= 1'b0;
		else
			lookup_valid_ic1 <= lookup_actual_ic0;
	generate
		if (ResetAll) begin : g_lookup_addr_ra
			always @(posedge clk_i)
				if (!rst_ni) begin
					lookup_addr_ic1 <= 1'sb0;
					fill_in_ic1 <= 1'sb0;
				end
				else if (lookup_grant_ic0) begin
					lookup_addr_ic1 <= lookup_addr_ic0[31:ibex_pkg_IC_INDEX_HI + 1];
					fill_in_ic1 <= fill_alloc_sel;
				end
		end
		else begin : g_lookup_addr_nr
			always @(posedge clk_i)
				if (lookup_grant_ic0) begin
					lookup_addr_ic1 <= lookup_addr_ic0[31:ibex_pkg_IC_INDEX_HI + 1];
					fill_in_ic1 <= fill_alloc_sel;
				end
		end
	endgenerate
	genvar way;
	generate
		for (way = 0; way < ibex_pkg_IC_NUM_WAYS; way = way + 1) begin : gen_tag_match
			assign tag_match_ic1[way] = tag_rdata_ic1[((1 - way) * TagSizeECC) + (ibex_pkg_IC_TAG_SIZE - 1)-:ibex_pkg_IC_TAG_SIZE] == {1'b1, lookup_addr_ic1[31:ibex_pkg_IC_INDEX_HI + 1]};
			assign tag_invalid_ic1[way] = ~tag_rdata_ic1[((1 - way) * TagSizeECC) + (ibex_pkg_IC_TAG_SIZE - 1)];
		end
	endgenerate
	assign tag_hit_ic1 = |tag_match_ic1;
	always @(*) begin
		hit_data_ecc_ic1 = 'b0;
		begin : sv2v_autoblock_1
			reg signed [31:0] way;
			for (way = 0; way < ibex_pkg_IC_NUM_WAYS; way = way + 1)
				if (tag_match_ic1[way])
					hit_data_ecc_ic1 = hit_data_ecc_ic1 | data_rdata_ic1[(1 - way) * LineSizeECC+:LineSizeECC];
		end
	end
	assign lowest_invalid_way_ic1[0] = tag_invalid_ic1[0];
	assign round_robin_way_ic1[0] = round_robin_way_q[1];
	generate
		for (way = 1; way < ibex_pkg_IC_NUM_WAYS; way = way + 1) begin : gen_lowest_way
			assign lowest_invalid_way_ic1[way] = tag_invalid_ic1[way] & ~|tag_invalid_ic1[way - 1:0];
			assign round_robin_way_ic1[way] = round_robin_way_q[way - 1];
		end
	endgenerate
	always @(posedge clk_i)
		if (!rst_ni)
			round_robin_way_q <= 2'b01;
		else if (lookup_valid_ic1)
			round_robin_way_q <= round_robin_way_ic1;
	assign sel_way_ic1 = (|tag_invalid_ic1 ? lowest_invalid_way_ic1 : round_robin_way_q);
	generate
		if (ICacheECC) begin : gen_data_ecc_checking
			wire [1:0] tag_err_ic1;
			wire [(ibex_pkg_IC_LINE_BEATS * 2) - 1:0] data_err_ic1;
			wire ecc_correction_write_d;
			reg ecc_correction_write_q;
			wire [1:0] ecc_correction_ways_d;
			reg [1:0] ecc_correction_ways_q;
			reg [ibex_pkg_IC_INDEX_W - 1:0] lookup_index_ic1;
			reg [ibex_pkg_IC_INDEX_W - 1:0] ecc_correction_index_q;
			genvar way;
			for (way = 0; way < ibex_pkg_IC_NUM_WAYS; way = way + 1) begin : gen_tag_ecc
				wire [1:0] tag_err_bank_ic1;
				wire [27:0] tag_rdata_padded_ic1;
				assign tag_rdata_padded_ic1 = {tag_rdata_ic1[((1 - way) * TagSizeECC) + (TagSizeECC - 1)-:6], {22 - ibex_pkg_IC_TAG_SIZE {1'b0}}, tag_rdata_ic1[((1 - way) * TagSizeECC) + (ibex_pkg_IC_TAG_SIZE - 1)-:ibex_pkg_IC_TAG_SIZE]};
				prim_secded_inv_28_22_dec data_ecc_dec(
					.data_i(tag_rdata_padded_ic1),
					.data_o(),
					.syndrome_o(),
					.err_o(tag_err_bank_ic1)
				);
				assign tag_err_ic1[way] = |tag_err_bank_ic1;
			end
			genvar bank;
			for (bank = 0; bank < ibex_pkg_IC_LINE_BEATS; bank = bank + 1) begin : gen_ecc_banks
				prim_secded_inv_39_32_dec data_ecc_dec(
					.data_i(hit_data_ecc_ic1[bank * BusSizeECC+:BusSizeECC]),
					.data_o(),
					.syndrome_o(),
					.err_o(data_err_ic1[bank * 2+:2])
				);
				assign hit_data_ic1[bank * ibex_pkg_BUS_SIZE+:ibex_pkg_BUS_SIZE] = hit_data_ecc_ic1[bank * BusSizeECC+:ibex_pkg_BUS_SIZE];
			end
			assign ecc_err_ic1 = lookup_valid_ic1 & ((|data_err_ic1 & tag_hit_ic1) | |tag_err_ic1);
			assign ecc_correction_ways_d = {ibex_pkg_IC_NUM_WAYS {|tag_err_ic1}} | (tag_match_ic1 & {ibex_pkg_IC_NUM_WAYS {|data_err_ic1}});
			assign ecc_correction_write_d = ecc_err_ic1;
			always @(posedge clk_i)
				if (!rst_ni)
					ecc_correction_write_q <= 1'b0;
				else
					ecc_correction_write_q <= ecc_correction_write_d;
			if (ResetAll) begin : g_lookup_ind_ra
				always @(posedge clk_i)
					if (!rst_ni)
						lookup_index_ic1 <= 1'sb0;
					else if (lookup_grant_ic0)
						lookup_index_ic1 <= lookup_addr_ic0[ibex_pkg_IC_INDEX_HI-:ibex_pkg_IC_INDEX_W];
			end
			else begin : g_lookup_ind_nr
				always @(posedge clk_i)
					if (lookup_grant_ic0)
						lookup_index_ic1 <= lookup_addr_ic0[ibex_pkg_IC_INDEX_HI-:ibex_pkg_IC_INDEX_W];
			end
			if (ResetAll) begin : g_ecc_correction_ra
				always @(posedge clk_i)
					if (!rst_ni) begin
						ecc_correction_ways_q <= 1'sb0;
						ecc_correction_index_q <= 1'sb0;
					end
					else if (ecc_err_ic1) begin
						ecc_correction_ways_q <= ecc_correction_ways_d;
						ecc_correction_index_q <= lookup_index_ic1;
					end
			end
			else begin : g_ecc_correction_nr
				always @(posedge clk_i)
					if (ecc_err_ic1) begin
						ecc_correction_ways_q <= ecc_correction_ways_d;
						ecc_correction_index_q <= lookup_index_ic1;
					end
			end
			assign ecc_write_req = ecc_correction_write_q;
			assign ecc_write_ways = ecc_correction_ways_q;
			assign ecc_write_index = ecc_correction_index_q;
			assign ecc_error_o = ecc_err_ic1;
		end
		else begin : gen_no_data_ecc
			assign ecc_err_ic1 = 1'b0;
			assign ecc_write_req = 1'b0;
			assign ecc_write_ways = 1'sb0;
			assign ecc_write_index = 1'sb0;
			assign hit_data_ic1 = hit_data_ecc_ic1;
			assign ecc_error_o = 1'b0;
		end
		if (BranchCache) begin : gen_caching_logic
			localparam [31:0] CACHE_AHEAD = 2;
			localparam [31:0] CACHE_CNT_W = 2;
			wire cache_cnt_dec;
			wire [1:0] cache_cnt_d;
			reg [1:0] cache_cnt_q;
			assign cache_cnt_dec = lookup_grant_ic0 & |cache_cnt_q;
			assign cache_cnt_d = (branch_i ? CACHE_AHEAD[1:0] : cache_cnt_q - {1'b0, cache_cnt_dec});
			always @(posedge clk_i)
				if (!rst_ni)
					cache_cnt_q <= 1'sb0;
				else
					cache_cnt_q <= cache_cnt_d;
			assign fill_cache_new = ((branch_i | |cache_cnt_q) & icache_enable_i) & ~inval_block_cache;
		end
		else begin : gen_cache_all
			assign fill_cache_new = icache_enable_i & ~inval_block_cache;
		end
	endgenerate
	always @(*) begin
		fb_fill_level = 1'sb0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < NUM_FB; i = i + 1)
				if (fill_busy_q[i] & ~fill_stale_q[i])
					fb_fill_level = fb_fill_level + 2'b01;
		end
	end
	assign fill_new_alloc = lookup_grant_ic0;
	assign fill_spec_req = (~icache_enable_i | branch_i) & ~|fill_ext_req;
	assign fill_spec_done = fill_spec_req & instr_gnt_i;
	assign fill_spec_hold = fill_spec_req & ~instr_gnt_i;
	genvar fb;
	generate
		for (fb = 0; fb < NUM_FB; fb = fb + 1) begin : gen_fbs
			if (fb == 0) begin : gen_fb_zero
				assign fill_alloc_sel[fb] = ~fill_busy_q[fb];
			end
			else begin : gen_fb_rest
				assign fill_alloc_sel[fb] = ~fill_busy_q[fb] & &fill_busy_q[fb - 1:0];
			end
			assign fill_alloc[fb] = fill_alloc_sel[fb] & fill_new_alloc;
			assign fill_busy_d[fb] = fill_alloc[fb] | (fill_busy_q[fb] & ~fill_done[fb]);
			assign fill_older_d[fb * NUM_FB+:NUM_FB] = (fill_alloc[fb] ? fill_busy_q : fill_older_q[fb * NUM_FB+:NUM_FB]) & ~fill_done;
			assign fill_done[fb] = ((((fill_ram_done_q[fb] | fill_hit_q[fb]) | ~fill_cache_q[fb]) | |fill_err_q[fb * ibex_pkg_IC_LINE_BEATS+:ibex_pkg_IC_LINE_BEATS]) & ((fill_out_done[fb] | fill_stale_q[fb]) | branch_i)) & fill_rvd_done[fb];
			assign fill_stale_d[fb] = fill_busy_q[fb] & (branch_i | fill_stale_q[fb]);
			assign fill_cache_d[fb] = (fill_alloc[fb] & fill_cache_new) | (((fill_cache_q[fb] & fill_busy_q[fb]) & icache_enable_i) & ~icache_inval_i);
			assign fill_hit_ic1[fb] = ((lookup_valid_ic1 & fill_in_ic1[fb]) & tag_hit_ic1) & ~ecc_err_ic1;
			assign fill_hit_d[fb] = fill_hit_ic1[fb] | (fill_hit_q[fb] & fill_busy_q[fb]);
			assign fill_ext_req[fb] = fill_busy_q[fb] & ~fill_ext_done_d[fb];
			assign fill_ext_cnt_d[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] = (fill_alloc[fb] ? {{ibex_pkg_IC_LINE_BEATS_W {1'b0}}, fill_spec_done} : fill_ext_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] + {{ibex_pkg_IC_LINE_BEATS_W {1'b0}}, fill_ext_arb[fb] & instr_gnt_i});
			assign fill_ext_hold_d[fb] = (fill_alloc[fb] & fill_spec_hold) | (fill_ext_arb[fb] & ~instr_gnt_i);
			assign fill_ext_done_d[fb] = ((((fill_ext_cnt_q[(fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : ibex_pkg_IC_LINE_BEATS_W - ibex_pkg_IC_LINE_BEATS_W)] | fill_hit_ic1[fb]) | fill_hit_q[fb]) | (~fill_cache_q[fb] & ((branch_i | fill_stale_q[fb]) | fill_ext_beat[(fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : ibex_pkg_IC_LINE_BEATS_W - ibex_pkg_IC_LINE_BEATS_W)]))) & ~fill_ext_hold_q[fb]) & fill_busy_q[fb];
			assign fill_rvd_exp[fb] = fill_busy_q[fb] & ~fill_rvd_done[fb];
			assign fill_rvd_cnt_d[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] = (fill_alloc[fb] ? {(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W) * 1 {1'sb0}} : fill_rvd_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] + {{ibex_pkg_IC_LINE_BEATS_W {1'b0}}, fill_rvd_arb[fb]});
			assign fill_rvd_done[fb] = (fill_ext_done_q[fb] & ~fill_ext_hold_q[fb]) & (fill_rvd_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] == fill_ext_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)]);
			assign fill_out_req[fb] = ((fill_busy_q[fb] & ~fill_stale_q[fb]) & ~fill_out_done[fb]) & (((fill_hit_ic1[fb] | fill_hit_q[fb]) | (fill_rvd_beat[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] > fill_out_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)])) | fill_rvd_arb[fb]);
			assign fill_out_grant[fb] = fill_out_arb[fb] & output_ready;
			assign fill_out_cnt_d[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] = (fill_alloc[fb] ? {1'b0, lookup_addr_ic0[2:ibex_pkg_BUS_W]} : fill_out_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] + {{ibex_pkg_IC_LINE_BEATS_W {1'b0}}, fill_out_grant[fb]});
			assign fill_out_done[fb] = fill_out_cnt_q[(fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : ibex_pkg_IC_LINE_BEATS_W - ibex_pkg_IC_LINE_BEATS_W)];
			assign fill_ram_req[fb] = ((((fill_busy_q[fb] & fill_rvd_cnt_q[(fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : ibex_pkg_IC_LINE_BEATS_W - ibex_pkg_IC_LINE_BEATS_W)]) & ~fill_hit_q[fb]) & fill_cache_q[fb]) & ~|fill_err_q[fb * ibex_pkg_IC_LINE_BEATS+:ibex_pkg_IC_LINE_BEATS]) & ~fill_ram_done_q[fb];
			assign fill_ram_done_d[fb] = fill_ram_arb[fb] | (fill_ram_done_q[fb] & fill_busy_q[fb]);
			assign fill_ext_beat[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] = {1'b0, fill_addr_q[fb][2:ibex_pkg_BUS_W]} + fill_ext_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : (ibex_pkg_IC_LINE_BEATS_W + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) - 1) : ibex_pkg_IC_LINE_BEATS_W - (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : (ibex_pkg_IC_LINE_BEATS_W + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) - 1)) : (((fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : (ibex_pkg_IC_LINE_BEATS_W + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) - 1) : ibex_pkg_IC_LINE_BEATS_W - (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : (ibex_pkg_IC_LINE_BEATS_W + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) - 1))) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) - 1)-:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)];
			assign fill_ext_off[fb * ibex_pkg_IC_LINE_BEATS_W+:ibex_pkg_IC_LINE_BEATS_W] = fill_ext_beat[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W - 1 : ibex_pkg_IC_LINE_BEATS_W - (ibex_pkg_IC_LINE_BEATS_W - 1)) : (((fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W - 1 : ibex_pkg_IC_LINE_BEATS_W - (ibex_pkg_IC_LINE_BEATS_W - 1))) + ibex_pkg_IC_LINE_BEATS_W) - 1)-:ibex_pkg_IC_LINE_BEATS_W];
			assign fill_rvd_beat[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] = {1'b0, fill_addr_q[fb][2:ibex_pkg_BUS_W]} + fill_rvd_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : (ibex_pkg_IC_LINE_BEATS_W + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) - 1) : ibex_pkg_IC_LINE_BEATS_W - (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : (ibex_pkg_IC_LINE_BEATS_W + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) - 1)) : (((fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : (ibex_pkg_IC_LINE_BEATS_W + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) - 1) : ibex_pkg_IC_LINE_BEATS_W - (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W : (ibex_pkg_IC_LINE_BEATS_W + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) - 1))) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) - 1)-:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)];
			assign fill_rvd_off[fb * ibex_pkg_IC_LINE_BEATS_W+:ibex_pkg_IC_LINE_BEATS_W] = fill_rvd_beat[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W - 1 : ibex_pkg_IC_LINE_BEATS_W - (ibex_pkg_IC_LINE_BEATS_W - 1)) : (((fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)) + (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W - 1 : ibex_pkg_IC_LINE_BEATS_W - (ibex_pkg_IC_LINE_BEATS_W - 1))) + ibex_pkg_IC_LINE_BEATS_W) - 1)-:ibex_pkg_IC_LINE_BEATS_W];
			assign fill_ext_arb[fb] = fill_ext_req[fb] & ~|(fill_ext_req & fill_older_q[fb * NUM_FB+:NUM_FB]);
			assign fill_ram_arb[fb] = (fill_ram_req[fb] & fill_grant_ic0) & ~|(fill_ram_req & fill_older_q[fb * NUM_FB+:NUM_FB]);
			assign fill_data_sel[fb] = ~|(((fill_busy_q & ~fill_out_done) & ~fill_stale_q) & fill_older_q[fb * NUM_FB+:NUM_FB]);
			assign fill_out_arb[fb] = fill_out_req[fb] & fill_data_sel[fb];
			assign fill_rvd_arb[fb] = (instr_rvalid_i & fill_rvd_exp[fb]) & ~|(fill_rvd_exp & fill_older_q[fb * NUM_FB+:NUM_FB]);
			assign fill_data_reg[fb] = (((fill_busy_q[fb] & ~fill_stale_q[fb]) & ~fill_out_done[fb]) & fill_data_sel[fb]) & (((fill_rvd_beat[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] > fill_out_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)]) | fill_hit_q[fb]) | |fill_err_q[fb * ibex_pkg_IC_LINE_BEATS+:ibex_pkg_IC_LINE_BEATS]);
			assign fill_data_hit[fb] = (fill_busy_q[fb] & fill_hit_ic1[fb]) & fill_data_sel[fb];
			assign fill_data_rvd[fb] = ((((((fill_busy_q[fb] & fill_rvd_arb[fb]) & ~fill_hit_q[fb]) & ~fill_hit_ic1[fb]) & ~fill_stale_q[fb]) & ~fill_out_done[fb]) & (fill_rvd_beat[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] == fill_out_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)])) & fill_data_sel[fb];
			assign fill_entry_en[fb] = fill_alloc[fb] | fill_busy_q[fb];
			always @(posedge clk_i)
				if (!rst_ni) begin
					fill_busy_q[fb] <= 1'b0;
					fill_older_q[fb * NUM_FB+:NUM_FB] <= 1'sb0;
					fill_stale_q[fb] <= 1'b0;
					fill_cache_q[fb] <= 1'b0;
					fill_hit_q[fb] <= 1'b0;
					fill_ext_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] <= 1'sb0;
					fill_ext_hold_q[fb] <= 1'b0;
					fill_ext_done_q[fb] <= 1'b0;
					fill_rvd_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] <= 1'sb0;
					fill_ram_done_q[fb] <= 1'b0;
					fill_out_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] <= 1'sb0;
				end
				else if (fill_entry_en[fb]) begin
					fill_busy_q[fb] <= fill_busy_d[fb];
					fill_older_q[fb * NUM_FB+:NUM_FB] <= fill_older_d[fb * NUM_FB+:NUM_FB];
					fill_stale_q[fb] <= fill_stale_d[fb];
					fill_cache_q[fb] <= fill_cache_d[fb];
					fill_hit_q[fb] <= fill_hit_d[fb];
					fill_ext_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] <= fill_ext_cnt_d[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)];
					fill_ext_hold_q[fb] <= fill_ext_hold_d[fb];
					fill_ext_done_q[fb] <= fill_ext_done_d[fb];
					fill_rvd_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] <= fill_rvd_cnt_d[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)];
					fill_ram_done_q[fb] <= fill_ram_done_d[fb];
					fill_out_cnt_q[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)] <= fill_out_cnt_d[(ibex_pkg_IC_LINE_BEATS_W >= 0 ? 0 : ibex_pkg_IC_LINE_BEATS_W) + (fb * (ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W))+:(ibex_pkg_IC_LINE_BEATS_W >= 0 ? ibex_pkg_IC_LINE_BEATS_W + 1 : 1 - ibex_pkg_IC_LINE_BEATS_W)];
				end
			assign fill_addr_en[fb] = fill_alloc[fb];
			assign fill_way_en[fb] = lookup_valid_ic1 & fill_in_ic1[fb];
			if (ResetAll) begin : g_fill_addr_ra
				always @(posedge clk_i)
					if (!rst_ni)
						fill_addr_q[fb] <= 1'sb0;
					else if (fill_addr_en[fb])
						fill_addr_q[fb] <= lookup_addr_ic0;
			end
			else begin : g_fill_addr_nr
				always @(posedge clk_i)
					if (fill_addr_en[fb])
						fill_addr_q[fb] <= lookup_addr_ic0;
			end
			always @(posedge clk_i)
				if (!rst_ni)
					fill_way_q[fb] <= 1'sb0;
				else if (fill_way_en[fb])
					fill_way_q[fb] <= sel_way_ic1;
			assign fill_data_d[fb] = (fill_hit_ic1[fb] ? hit_data_ic1 : {ibex_pkg_IC_LINE_BEATS {instr_rdata_i}});
			genvar b;
			for (b = 0; b < ibex_pkg_IC_LINE_BEATS; b = b + 1) begin : gen_data_buf
				assign fill_err_d[(fb * ibex_pkg_IC_LINE_BEATS) + b] = ((fill_rvd_arb[fb] & instr_err_i) & (fill_rvd_off[fb * ibex_pkg_IC_LINE_BEATS_W+:ibex_pkg_IC_LINE_BEATS_W] == b[ibex_pkg_IC_LINE_BEATS_W - 1:0])) | (fill_busy_q[fb] & fill_err_q[(fb * ibex_pkg_IC_LINE_BEATS) + b]);
				always @(posedge clk_i)
					if (!rst_ni)
						fill_err_q[(fb * ibex_pkg_IC_LINE_BEATS) + b] <= 1'sb0;
					else if (fill_entry_en[fb])
						fill_err_q[(fb * ibex_pkg_IC_LINE_BEATS) + b] <= fill_err_d[(fb * ibex_pkg_IC_LINE_BEATS) + b];
				assign fill_data_en[(fb * ibex_pkg_IC_LINE_BEATS) + b] = fill_hit_ic1[fb] | ((fill_rvd_arb[fb] & ~fill_hit_q[fb]) & (fill_rvd_off[fb * ibex_pkg_IC_LINE_BEATS_W+:ibex_pkg_IC_LINE_BEATS_W] == b[ibex_pkg_IC_LINE_BEATS_W - 1:0]));
				if (ResetAll) begin : g_fill_data_ra
					always @(posedge clk_i)
						if (!rst_ni)
							fill_data_q[fb][b * ibex_pkg_BUS_SIZE+:ibex_pkg_BUS_SIZE] <= 1'sb0;
						else if (fill_data_en[(fb * ibex_pkg_IC_LINE_BEATS) + b])
							fill_data_q[fb][b * ibex_pkg_BUS_SIZE+:ibex_pkg_BUS_SIZE] <= fill_data_d[fb][b * ibex_pkg_BUS_SIZE+:ibex_pkg_BUS_SIZE];
				end
				else begin : g_fill_data_nr
					always @(posedge clk_i)
						if (fill_data_en[(fb * ibex_pkg_IC_LINE_BEATS) + b])
							fill_data_q[fb][b * ibex_pkg_BUS_SIZE+:ibex_pkg_BUS_SIZE] <= fill_data_d[fb][b * ibex_pkg_BUS_SIZE+:ibex_pkg_BUS_SIZE];
				end
			end
		end
	endgenerate
	always @(*) begin
		fill_ext_req_addr = 1'sb0;
		begin : sv2v_autoblock_3
			reg signed [31:0] i;
			for (i = 0; i < NUM_FB; i = i + 1)
				if (fill_ext_arb[i])
					fill_ext_req_addr = fill_ext_req_addr | {fill_addr_q[i][31:ibex_pkg_IC_LINE_W], fill_ext_off[i * ibex_pkg_IC_LINE_BEATS_W+:ibex_pkg_IC_LINE_BEATS_W]};
		end
	end
	always @(*) begin
		fill_ram_req_addr = 1'sb0;
		fill_ram_req_way = 1'sb0;
		fill_ram_req_data = 1'sb0;
		begin : sv2v_autoblock_4
			reg signed [31:0] i;
			for (i = 0; i < NUM_FB; i = i + 1)
				if (fill_ram_arb[i]) begin
					fill_ram_req_addr = fill_ram_req_addr | fill_addr_q[i];
					fill_ram_req_way = fill_ram_req_way | fill_way_q[i];
					fill_ram_req_data = fill_ram_req_data | fill_data_q[i];
				end
		end
	end
	always @(*) begin
		fill_out_data = 1'sb0;
		fill_out_err = 1'sb0;
		begin : sv2v_autoblock_5
			reg signed [31:0] i;
			for (i = 0; i < NUM_FB; i = i + 1)
				if (fill_data_reg[i]) begin
					fill_out_data = fill_out_data | fill_data_q[i];
					fill_out_err = fill_out_err | (fill_err_q[i * ibex_pkg_IC_LINE_BEATS+:ibex_pkg_IC_LINE_BEATS] & ~{ibex_pkg_IC_LINE_BEATS {fill_hit_q[i]}});
				end
		end
	end
	assign instr_req = ((~icache_enable_i | branch_i) & lookup_grant_ic0) | |fill_ext_req;
	assign instr_addr = (|fill_ext_req ? fill_ext_req_addr : lookup_addr_ic0[31:ibex_pkg_BUS_W]);
	assign instr_req_o = instr_req;
	assign instr_addr_o = {instr_addr[31:ibex_pkg_BUS_W], {ibex_pkg_BUS_W {1'b0}}};
	assign line_data = (|fill_data_hit ? hit_data_ic1 : fill_out_data);
	assign line_err = (|fill_data_hit ? {ibex_pkg_IC_LINE_BEATS {1'b0}} : fill_out_err);
	always @(*) begin
		line_data_muxed = 1'sb0;
		line_err_muxed = 1'b0;
		begin : sv2v_autoblock_6
			reg [31:0] i;
			for (i = 0; i < ibex_pkg_IC_LINE_BEATS; i = i + 1)
				if ((output_addr_q[2:ibex_pkg_BUS_W] + {{ibex_pkg_IC_LINE_BEATS_W - 1 {1'b0}}, skid_valid_q}) == i[ibex_pkg_IC_LINE_BEATS_W - 1:0]) begin
					line_data_muxed = line_data_muxed | line_data[i * 32+:32];
					line_err_muxed = line_err_muxed | line_err[i];
				end
		end
	end
	assign output_data = (|fill_data_rvd ? instr_rdata_i : line_data_muxed);
	assign output_err = (|fill_data_rvd ? instr_err_i : line_err_muxed);
	assign data_valid = |fill_out_arb;
	assign skid_data_d = output_data[31:16];
	assign skid_en = data_valid & (ready_i | skid_ready);
	generate
		if (ResetAll) begin : g_skid_data_ra
			always @(posedge clk_i)
				if (!rst_ni) begin
					skid_data_q <= 1'sb0;
					skid_err_q <= 1'sb0;
				end
				else if (skid_en) begin
					skid_data_q <= skid_data_d;
					skid_err_q <= output_err;
				end
		end
		else begin : g_skid_data_nr
			always @(posedge clk_i)
				if (skid_en) begin
					skid_data_q <= skid_data_d;
					skid_err_q <= output_err;
				end
		end
	endgenerate
	assign skid_complete_instr = skid_valid_q & ((skid_data_q[1:0] != 2'b11) | skid_err_q);
	assign skid_ready = (output_addr_q[1] & ~skid_valid_q) & (~output_compressed | output_err);
	assign output_ready = (ready_i | skid_ready) & ~skid_complete_instr;
	assign output_compressed = rdata_o[1:0] != 2'b11;
	assign skid_valid_d = (branch_i ? 1'b0 : (skid_valid_q ? ~(ready_i & ((skid_data_q[1:0] != 2'b11) | skid_err_q)) : data_valid & ((output_addr_q[1] & (~output_compressed | output_err)) | (((~output_addr_q[1] & output_compressed) & ~output_err) & ready_i))));
	always @(posedge clk_i)
		if (!rst_ni)
			skid_valid_q <= 1'b0;
		else
			skid_valid_q <= skid_valid_d;
	assign output_valid = skid_complete_instr | (data_valid & (((~output_addr_q[1] | skid_valid_q) | output_err) | (output_data[17:16] != 2'b11)));
	assign output_addr_en = branch_i | (ready_i & valid_o);
	assign addr_incr_two = output_compressed & ~err_o;
	assign output_addr_incr = output_addr_q[31:1] + {29'd0, ~addr_incr_two, addr_incr_two};
	assign output_addr_d = (branch_i ? addr_i[31:1] : output_addr_incr);
	generate
		if (ResetAll) begin : g_output_addr_ra
			always @(posedge clk_i)
				if (!rst_ni)
					output_addr_q <= 1'sb0;
				else if (output_addr_en)
					output_addr_q <= output_addr_d;
		end
		else begin : g_output_addr_nr
			always @(posedge clk_i)
				if (output_addr_en)
					output_addr_q <= output_addr_d;
		end
	endgenerate
	localparam [31:0] ibex_pkg_IC_OUTPUT_BEATS = 2;
	always @(*) begin
		output_data_lo = 1'sb0;
		begin : sv2v_autoblock_7
			reg [31:0] i;
			for (i = 0; i < ibex_pkg_IC_OUTPUT_BEATS; i = i + 1)
				if (output_addr_q[1:1] == i[0:0])
					output_data_lo = output_data_lo | output_data[i * 16+:16];
		end
	end
	always @(*) begin
		output_data_hi = 1'sb0;
		begin : sv2v_autoblock_8
			reg [31:0] i;
			for (i = 0; i < 1; i = i + 1)
				if (output_addr_q[1:1] == i[0:0])
					output_data_hi = output_data_hi | output_data[(i + 1) * 16+:16];
		end
		if (&output_addr_q[1:1])
			output_data_hi = output_data_hi | output_data[15:0];
	end
	assign valid_o = output_valid;
	assign rdata_o = {output_data_hi, (skid_valid_q ? skid_data_q : output_data_lo)};
	assign addr_o = {output_addr_q, 1'b0};
	assign err_o = (skid_valid_q & skid_err_q) | (~skid_complete_instr & output_err);
	assign err_plus2_o = skid_valid_q & ~skid_err_q;
	always @(*) begin
		inval_state_d = inval_state_q;
		inval_index_d = inval_index_q;
		inval_index_en = 1'b0;
		inval_write_req = 1'b0;
		ic_scr_key_req_o = 1'b0;
		inval_block_cache = 1'b1;
		case (inval_state_q)
			2'd0: begin
				inval_state_d = 2'd1;
				if (~ic_scr_key_valid_i)
					ic_scr_key_req_o = 1'b1;
			end
			2'd1:
				if (ic_scr_key_valid_i) begin
					inval_state_d = 2'd2;
					inval_index_d = 1'sb0;
					inval_index_en = 1'b1;
				end
			2'd2: begin
				inval_write_req = 1'b1;
				inval_index_d = inval_index_q + {{ibex_pkg_IC_INDEX_W - 1 {1'b0}}, 1'b1};
				inval_index_en = 1'b1;
				if (icache_inval_i) begin
					ic_scr_key_req_o = 1'b1;
					inval_state_d = 2'd1;
				end
				else if (&inval_index_q)
					inval_state_d = 2'd3;
			end
			2'd3:
				if (icache_inval_i) begin
					ic_scr_key_req_o = 1'b1;
					inval_state_d = 2'd1;
				end
				else
					inval_block_cache = 1'b0;
			default:
				;
		endcase
	end
	assign inval_active = inval_state_q != 2'd3;
	always @(posedge clk_i)
		if (!rst_ni)
			inval_state_q <= 2'd0;
		else
			inval_state_q <= inval_state_d;
	generate
		if (ResetAll) begin : g_inval_index_ra
			always @(posedge clk_i)
				if (!rst_ni)
					inval_index_q <= 1'sb0;
				else if (inval_index_en)
					inval_index_q <= inval_index_d;
		end
		else begin : g_inval_index_nr
			always @(posedge clk_i)
				if (inval_index_en)
					inval_index_q <= inval_index_d;
		end
	endgenerate
	assign busy_o = inval_active | |(fill_busy_q & ~fill_rvd_done);
endmodule
module ibex_controller (
	clk_i,
	rst_ni,
	ctrl_busy_o,
	illegal_insn_i,
	ecall_insn_i,
	mret_insn_i,
	dret_insn_i,
	wfi_insn_i,
	ebrk_insn_i,
	csr_pipe_flush_i,
	instr_valid_i,
	instr_i,
	instr_compressed_i,
	instr_is_compressed_i,
	instr_bp_taken_i,
	instr_fetch_err_i,
	instr_fetch_err_plus2_i,
	pc_id_i,
	instr_valid_clear_o,
	id_in_ready_o,
	controller_run_o,
	instr_exec_i,
	instr_req_o,
	pc_set_o,
	pc_mux_o,
	nt_branch_mispredict_o,
	exc_pc_mux_o,
	exc_cause_o,
	lsu_addr_last_i,
	load_err_i,
	store_err_i,
	mem_resp_intg_err_i,
	wb_exception_o,
	id_exception_o,
	branch_set_i,
	branch_not_set_i,
	jump_set_i,
	csr_mstatus_mie_i,
	irq_pending_i,
	irqs_i,
	irq_nm_ext_i,
	nmi_mode_o,
	debug_req_i,
	debug_cause_o,
	debug_csr_save_o,
	debug_mode_o,
	debug_mode_entering_o,
	debug_single_step_i,
	debug_ebreakm_i,
	debug_ebreaku_i,
	trigger_match_i,
	csr_save_if_o,
	csr_save_id_o,
	csr_save_wb_o,
	csr_restore_mret_id_o,
	csr_restore_dret_id_o,
	csr_save_cause_o,
	csr_mtval_o,
	priv_mode_i,
	stall_id_i,
	stall_wb_i,
	flush_id_o,
	ready_wb_i,
	perf_jump_o,
	perf_tbranch_o
);
	parameter [0:0] WritebackStage = 1'b0;
	parameter [0:0] BranchPredictor = 1'b0;
	parameter [0:0] MemECC = 1'b0;
	input wire clk_i;
	input wire rst_ni;
	output reg ctrl_busy_o;
	input wire illegal_insn_i;
	input wire ecall_insn_i;
	input wire mret_insn_i;
	input wire dret_insn_i;
	input wire wfi_insn_i;
	input wire ebrk_insn_i;
	input wire csr_pipe_flush_i;
	input wire instr_valid_i;
	input wire [31:0] instr_i;
	input wire [15:0] instr_compressed_i;
	input wire instr_is_compressed_i;
	input wire instr_bp_taken_i;
	input wire instr_fetch_err_i;
	input wire instr_fetch_err_plus2_i;
	input wire [31:0] pc_id_i;
	output wire instr_valid_clear_o;
	output wire id_in_ready_o;
	output reg controller_run_o;
	input wire instr_exec_i;
	output reg instr_req_o;
	output reg pc_set_o;
	output reg [2:0] pc_mux_o;
	output reg nt_branch_mispredict_o;
	output reg [1:0] exc_pc_mux_o;
	output reg [6:0] exc_cause_o;
	input wire [31:0] lsu_addr_last_i;
	input wire load_err_i;
	input wire store_err_i;
	input wire mem_resp_intg_err_i;
	output wire wb_exception_o;
	output wire id_exception_o;
	input wire branch_set_i;
	input wire branch_not_set_i;
	input wire jump_set_i;
	input wire csr_mstatus_mie_i;
	input wire irq_pending_i;
	input wire [17:0] irqs_i;
	input wire irq_nm_ext_i;
	output wire nmi_mode_o;
	input wire debug_req_i;
	output wire [2:0] debug_cause_o;
	output reg debug_csr_save_o;
	output wire debug_mode_o;
	output reg debug_mode_entering_o;
	input wire debug_single_step_i;
	input wire debug_ebreakm_i;
	input wire debug_ebreaku_i;
	input wire trigger_match_i;
	output reg csr_save_if_o;
	output reg csr_save_id_o;
	output reg csr_save_wb_o;
	output reg csr_restore_mret_id_o;
	output reg csr_restore_dret_id_o;
	output reg csr_save_cause_o;
	output reg [31:0] csr_mtval_o;
	input wire [1:0] priv_mode_i;
	input wire stall_id_i;
	input wire stall_wb_i;
	output wire flush_id_o;
	input wire ready_wb_i;
	output reg perf_jump_o;
	output reg perf_tbranch_o;
	reg [3:0] ctrl_fsm_cs;
	reg [3:0] ctrl_fsm_ns;
	reg nmi_mode_q;
	reg nmi_mode_d;
	reg debug_mode_q;
	reg debug_mode_d;
	wire [2:0] debug_cause_d;
	reg [2:0] debug_cause_q;
	reg load_err_q;
	wire load_err_d;
	reg store_err_q;
	wire store_err_d;
	reg exc_req_q;
	wire exc_req_d;
	reg illegal_insn_q;
	wire illegal_insn_d;
	reg instr_fetch_err_prio;
	reg illegal_insn_prio;
	reg ecall_insn_prio;
	reg ebrk_insn_prio;
	reg store_err_prio;
	reg load_err_prio;
	wire stall;
	reg halt_if;
	reg retain_id;
	reg flush_id;
	wire exc_req_lsu;
	wire special_req;
	wire special_req_pc_change;
	wire special_req_flush_only;
	wire do_single_step_d;
	reg do_single_step_q;
	wire enter_debug_mode_prio_d;
	reg enter_debug_mode_prio_q;
	wire enter_debug_mode;
	wire ebreak_into_debug;
	wire irq_enabled;
	wire handle_irq;
	wire id_wb_pending;
	wire irq_nm;
	wire irq_nm_int;
	wire [31:0] irq_nm_int_mtval;
	wire [4:0] irq_nm_int_cause;
	reg [3:0] mfip_id;
	wire unused_irq_timer;
	wire ecall_insn;
	wire mret_insn;
	wire dret_insn;
	wire wfi_insn;
	wire ebrk_insn;
	wire csr_pipe_flush;
	wire instr_fetch_err;
	assign load_err_d = load_err_i;
	assign store_err_d = store_err_i;
	assign ecall_insn = ecall_insn_i & instr_valid_i;
	assign mret_insn = mret_insn_i & instr_valid_i;
	assign dret_insn = dret_insn_i & instr_valid_i;
	assign wfi_insn = wfi_insn_i & instr_valid_i;
	assign ebrk_insn = ebrk_insn_i & instr_valid_i;
	assign csr_pipe_flush = csr_pipe_flush_i & instr_valid_i;
	assign instr_fetch_err = instr_fetch_err_i & instr_valid_i;
	assign illegal_insn_d = illegal_insn_i & (ctrl_fsm_cs != 4'd6);
	assign exc_req_d = (((ecall_insn | ebrk_insn) | illegal_insn_d) | instr_fetch_err) & (ctrl_fsm_cs != 4'd6);
	assign exc_req_lsu = store_err_i | load_err_i;
	assign id_exception_o = exc_req_d & ~wb_exception_o;
	assign special_req_flush_only = wfi_insn | csr_pipe_flush;
	assign special_req_pc_change = ((mret_insn | dret_insn) | exc_req_d) | exc_req_lsu;
	assign special_req = special_req_pc_change | special_req_flush_only;
	assign id_wb_pending = instr_valid_i | ~ready_wb_i;
	generate
		if (WritebackStage) begin : g_wb_exceptions
			always @(*) begin
				instr_fetch_err_prio = 0;
				illegal_insn_prio = 0;
				ecall_insn_prio = 0;
				ebrk_insn_prio = 0;
				store_err_prio = 0;
				load_err_prio = 0;
				if (store_err_q)
					store_err_prio = 1'b1;
				else if (load_err_q)
					load_err_prio = 1'b1;
				else if (instr_fetch_err)
					instr_fetch_err_prio = 1'b1;
				else if (illegal_insn_q)
					illegal_insn_prio = 1'b1;
				else if (ecall_insn)
					ecall_insn_prio = 1'b1;
				else if (ebrk_insn)
					ebrk_insn_prio = 1'b1;
			end
			assign wb_exception_o = ((load_err_q | store_err_q) | load_err_i) | store_err_i;
		end
		else begin : g_no_wb_exceptions
			always @(*) begin
				instr_fetch_err_prio = 0;
				illegal_insn_prio = 0;
				ecall_insn_prio = 0;
				ebrk_insn_prio = 0;
				store_err_prio = 0;
				load_err_prio = 0;
				if (instr_fetch_err)
					instr_fetch_err_prio = 1'b1;
				else if (illegal_insn_q)
					illegal_insn_prio = 1'b1;
				else if (ecall_insn)
					ecall_insn_prio = 1'b1;
				else if (ebrk_insn)
					ebrk_insn_prio = 1'b1;
				else if (store_err_q)
					store_err_prio = 1'b1;
				else if (load_err_q)
					load_err_prio = 1'b1;
			end
			assign wb_exception_o = 1'b0;
		end
		if (MemECC) begin : g_intg_irq_int
			reg mem_resp_intg_err_irq_pending_q;
			wire mem_resp_intg_err_irq_pending_d;
			reg [31:0] mem_resp_intg_err_addr_q;
			reg [31:0] mem_resp_intg_err_addr_d;
			reg mem_resp_intg_err_irq_set;
			reg mem_resp_intg_err_irq_clear;
			wire entering_nmi;
			assign entering_nmi = nmi_mode_d & ~nmi_mode_q;
			always @(*) begin
				mem_resp_intg_err_addr_d = mem_resp_intg_err_addr_q;
				mem_resp_intg_err_irq_set = 1'b0;
				mem_resp_intg_err_irq_clear = 1'b0;
				if (mem_resp_intg_err_irq_pending_q) begin
					if (entering_nmi & !irq_nm_ext_i)
						mem_resp_intg_err_irq_clear = 1'b1;
				end
				else if (mem_resp_intg_err_i) begin
					mem_resp_intg_err_addr_d = lsu_addr_last_i;
					mem_resp_intg_err_irq_set = 1'b1;
				end
			end
			assign mem_resp_intg_err_irq_pending_d = (mem_resp_intg_err_irq_pending_q & ~mem_resp_intg_err_irq_clear) | mem_resp_intg_err_irq_set;
			always @(posedge clk_i)
				if (!rst_ni) begin
					mem_resp_intg_err_irq_pending_q <= 1'b0;
					mem_resp_intg_err_addr_q <= 1'sb0;
				end
				else begin
					mem_resp_intg_err_irq_pending_q <= mem_resp_intg_err_irq_pending_d;
					mem_resp_intg_err_addr_q <= mem_resp_intg_err_addr_d;
				end
			assign irq_nm_int = mem_resp_intg_err_irq_set | mem_resp_intg_err_irq_pending_q;
			assign irq_nm_int_cause = 5'b00000;
			assign irq_nm_int_mtval = mem_resp_intg_err_addr_q;
		end
		else begin : g_no_intg_irq_int
			wire unused_mem_resp_intg_err_i;
			assign unused_mem_resp_intg_err_i = mem_resp_intg_err_i;
			assign irq_nm_int = 1'b0;
			assign irq_nm_int_cause = 5'd0;
			assign irq_nm_int_mtval = 1'sb0;
		end
	endgenerate
	assign do_single_step_d = (instr_valid_i ? ~debug_mode_q & debug_single_step_i : do_single_step_q);
	assign enter_debug_mode_prio_d = (debug_req_i | do_single_step_d) & ~debug_mode_q;
	assign enter_debug_mode = enter_debug_mode_prio_d | (trigger_match_i & ~debug_mode_q);
	assign ebreak_into_debug = (priv_mode_i == 2'b11 ? debug_ebreakm_i : (priv_mode_i == 2'b00 ? debug_ebreaku_i : 1'b0));
	assign irq_nm = irq_nm_ext_i | irq_nm_int;
	assign irq_enabled = csr_mstatus_mie_i | (priv_mode_i == 2'b00);
	assign handle_irq = ((~debug_mode_q & ~debug_single_step_i) & ~nmi_mode_q) & (irq_nm | (irq_pending_i & irq_enabled));
	always @(*) begin : gen_mfip_id
		mfip_id = 4'd0;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 14; i >= 0; i = i - 1)
				if (irqs_i[0 + i])
					mfip_id = i[3:0];
		end
	end
	assign unused_irq_timer = irqs_i[16];
	assign debug_cause_d = (trigger_match_i ? 3'h2 : (ebrk_insn_prio & ebreak_into_debug ? 3'h1 : (debug_req_i ? 3'h3 : (do_single_step_d ? 3'h4 : 3'h0))));
	always @(posedge clk_i)
		if (!rst_ni)
			debug_cause_q <= 3'h0;
		else
			debug_cause_q <= debug_cause_d;
	assign debug_cause_o = debug_cause_q;
	localparam [6:0] ibex_pkg_ExcCauseBreakpoint = 7'h03;
	localparam [6:0] ibex_pkg_ExcCauseEcallMMode = 7'h0b;
	localparam [6:0] ibex_pkg_ExcCauseEcallUMode = 7'h08;
	localparam [6:0] ibex_pkg_ExcCauseIllegalInsn = 7'h02;
	localparam [6:0] ibex_pkg_ExcCauseInsnAddrMisa = 7'h00;
	localparam [6:0] ibex_pkg_ExcCauseInstrAccessFault = 7'h01;
	localparam [6:0] ibex_pkg_ExcCauseIrqExternalM = 7'h2b;
	localparam [6:0] ibex_pkg_ExcCauseIrqNm = 7'h3f;
	localparam [6:0] ibex_pkg_ExcCauseIrqSoftwareM = 7'h23;
	localparam [6:0] ibex_pkg_ExcCauseIrqTimerM = 7'h27;
	localparam [6:0] ibex_pkg_ExcCauseLoadAccessFault = 7'h05;
	localparam [6:0] ibex_pkg_ExcCauseStoreAccessFault = 7'h07;
	function automatic [4:0] sv2v_cast_5;
		input reg [4:0] inp;
		sv2v_cast_5 = inp;
	endfunction
	always @(*) begin
		instr_req_o = 1'b1;
		csr_save_if_o = 1'b0;
		csr_save_id_o = 1'b0;
		csr_save_wb_o = 1'b0;
		csr_restore_mret_id_o = 1'b0;
		csr_restore_dret_id_o = 1'b0;
		csr_save_cause_o = 1'b0;
		csr_mtval_o = 1'sb0;
		pc_mux_o = 3'd0;
		pc_set_o = 1'b0;
		nt_branch_mispredict_o = 1'b0;
		exc_pc_mux_o = 2'd1;
		exc_cause_o = ibex_pkg_ExcCauseInsnAddrMisa;
		ctrl_fsm_ns = ctrl_fsm_cs;
		ctrl_busy_o = 1'b1;
		halt_if = 1'b0;
		retain_id = 1'b0;
		flush_id = 1'b0;
		debug_csr_save_o = 1'b0;
		debug_mode_d = debug_mode_q;
		debug_mode_entering_o = 1'b0;
		nmi_mode_d = nmi_mode_q;
		perf_tbranch_o = 1'b0;
		perf_jump_o = 1'b0;
		controller_run_o = 1'b0;
		case (ctrl_fsm_cs)
			4'd0: begin
				instr_req_o = 1'b0;
				pc_mux_o = 3'd0;
				pc_set_o = 1'b1;
				ctrl_fsm_ns = 4'd1;
			end
			4'd1: begin
				instr_req_o = 1'b1;
				pc_mux_o = 3'd0;
				pc_set_o = 1'b1;
				ctrl_fsm_ns = 4'd4;
			end
			4'd2: begin
				ctrl_busy_o = 1'b0;
				instr_req_o = 1'b0;
				halt_if = 1'b1;
				flush_id = 1'b1;
				ctrl_fsm_ns = 4'd3;
			end
			4'd3: begin
				instr_req_o = 1'b0;
				halt_if = 1'b1;
				flush_id = 1'b1;
				if ((((irq_nm || irq_pending_i) || debug_req_i) || debug_mode_q) || debug_single_step_i)
					ctrl_fsm_ns = 4'd4;
				else
					ctrl_busy_o = 1'b0;
			end
			4'd4: begin
				if (id_in_ready_o)
					ctrl_fsm_ns = 4'd5;
				if (handle_irq) begin
					ctrl_fsm_ns = 4'd7;
					halt_if = 1'b1;
				end
				if (enter_debug_mode) begin
					ctrl_fsm_ns = 4'd8;
					halt_if = 1'b1;
				end
			end
			4'd5: begin
				controller_run_o = 1'b1;
				pc_mux_o = 3'd1;
				if (special_req) begin
					retain_id = 1'b1;
					if (ready_wb_i | wb_exception_o)
						ctrl_fsm_ns = 4'd6;
				end
				if (branch_set_i || jump_set_i) begin
					pc_set_o = (BranchPredictor ? ~instr_bp_taken_i : 1'b1);
					perf_tbranch_o = branch_set_i;
					perf_jump_o = jump_set_i;
				end
				if (BranchPredictor) begin
					if (instr_bp_taken_i & branch_not_set_i)
						nt_branch_mispredict_o = 1'b1;
				end
				if ((enter_debug_mode || handle_irq) && (stall || id_wb_pending))
					halt_if = 1'b1;
				if ((!stall && !special_req) && !id_wb_pending) begin
					if (enter_debug_mode) begin
						ctrl_fsm_ns = 4'd8;
						halt_if = 1'b1;
					end
					else if (handle_irq) begin
						ctrl_fsm_ns = 4'd7;
						halt_if = 1'b1;
					end
				end
			end
			4'd7: begin
				pc_mux_o = 3'd2;
				exc_pc_mux_o = 2'd1;
				if (handle_irq) begin
					pc_set_o = 1'b1;
					csr_save_if_o = 1'b1;
					csr_save_cause_o = 1'b1;
					if (irq_nm && !nmi_mode_q) begin
						exc_cause_o = (irq_nm_ext_i ? ibex_pkg_ExcCauseIrqNm : {2'b10, irq_nm_int_cause});
						if (irq_nm_int & !irq_nm_ext_i)
							csr_mtval_o = irq_nm_int_mtval;
						nmi_mode_d = 1'b1;
					end
					else if (irqs_i[14-:15] != 15'b000000000000000)
						exc_cause_o = {2'b01, sv2v_cast_5({1'b1, mfip_id})};
					else if (irqs_i[15])
						exc_cause_o = ibex_pkg_ExcCauseIrqExternalM;
					else if (irqs_i[17])
						exc_cause_o = ibex_pkg_ExcCauseIrqSoftwareM;
					else
						exc_cause_o = ibex_pkg_ExcCauseIrqTimerM;
				end
				ctrl_fsm_ns = 4'd5;
			end
			4'd8: begin
				pc_mux_o = 3'd2;
				exc_pc_mux_o = 2'd2;
				flush_id = 1'b1;
				pc_set_o = 1'b1;
				csr_save_if_o = 1'b1;
				debug_csr_save_o = 1'b1;
				csr_save_cause_o = 1'b1;
				debug_mode_d = 1'b1;
				debug_mode_entering_o = 1'b1;
				ctrl_fsm_ns = 4'd5;
			end
			4'd9: begin
				flush_id = 1'b1;
				pc_mux_o = 3'd2;
				pc_set_o = 1'b1;
				exc_pc_mux_o = 2'd2;
				if (ebreak_into_debug && !debug_mode_q) begin
					csr_save_cause_o = 1'b1;
					csr_save_id_o = 1'b1;
					debug_csr_save_o = 1'b1;
				end
				debug_mode_d = 1'b1;
				debug_mode_entering_o = 1'b1;
				ctrl_fsm_ns = 4'd5;
			end
			4'd6: begin
				halt_if = 1'b1;
				flush_id = 1'b1;
				ctrl_fsm_ns = 4'd5;
				if ((exc_req_q || store_err_q) || load_err_q) begin
					pc_set_o = 1'b1;
					pc_mux_o = 3'd2;
					exc_pc_mux_o = (debug_mode_q ? 2'd3 : 2'd0);
					if (WritebackStage) begin : g_writeback_mepc_save
						csr_save_id_o = ~(store_err_q | load_err_q);
						csr_save_wb_o = store_err_q | load_err_q;
					end
					else begin : g_no_writeback_mepc_save
						csr_save_id_o = 1'b0;
					end
					csr_save_cause_o = 1'b1;
					case (1'b1)
						instr_fetch_err_prio: begin
							exc_cause_o = ibex_pkg_ExcCauseInstrAccessFault;
							csr_mtval_o = (instr_fetch_err_plus2_i ? pc_id_i + 32'd2 : pc_id_i);
						end
						illegal_insn_prio: begin
							exc_cause_o = ibex_pkg_ExcCauseIllegalInsn;
							csr_mtval_o = (instr_is_compressed_i ? {16'b0000000000000000, instr_compressed_i} : instr_i);
						end
						ecall_insn_prio: exc_cause_o = (priv_mode_i == 2'b11 ? ibex_pkg_ExcCauseEcallMMode : ibex_pkg_ExcCauseEcallUMode);
						ebrk_insn_prio:
							if (debug_mode_q | ebreak_into_debug) begin
								pc_set_o = 1'b0;
								csr_save_id_o = 1'b0;
								csr_save_cause_o = 1'b0;
								ctrl_fsm_ns = 4'd9;
								flush_id = 1'b0;
							end
							else
								exc_cause_o = ibex_pkg_ExcCauseBreakpoint;
						store_err_prio: begin
							exc_cause_o = ibex_pkg_ExcCauseStoreAccessFault;
							csr_mtval_o = lsu_addr_last_i;
						end
						load_err_prio: begin
							exc_cause_o = ibex_pkg_ExcCauseLoadAccessFault;
							csr_mtval_o = lsu_addr_last_i;
						end
						default:
							;
					endcase
				end
				else if (mret_insn) begin
					pc_mux_o = 3'd3;
					pc_set_o = 1'b1;
					csr_restore_mret_id_o = 1'b1;
					if (nmi_mode_q)
						nmi_mode_d = 1'b0;
				end
				else if (dret_insn) begin
					pc_mux_o = 3'd4;
					pc_set_o = 1'b1;
					debug_mode_d = 1'b0;
					csr_restore_dret_id_o = 1'b1;
				end
				else if (wfi_insn)
					ctrl_fsm_ns = 4'd2;
				if (enter_debug_mode_prio_q && !(ebrk_insn_prio && ebreak_into_debug))
					ctrl_fsm_ns = 4'd8;
			end
			default: begin
				instr_req_o = 1'b0;
				ctrl_fsm_ns = 4'd0;
			end
		endcase
		if (~instr_exec_i)
			halt_if = 1'b1;
	end
	assign flush_id_o = flush_id;
	assign debug_mode_o = debug_mode_q;
	assign nmi_mode_o = nmi_mode_q;
	assign stall = stall_id_i | stall_wb_i;
	assign id_in_ready_o = (~stall & ~halt_if) & ~retain_id;
	assign instr_valid_clear_o = ~(stall | retain_id) | flush_id;
	always @(posedge clk_i) begin : update_regs
		if (!rst_ni) begin
			ctrl_fsm_cs <= 4'd0;
			nmi_mode_q <= 1'b0;
			do_single_step_q <= 1'b0;
			debug_mode_q <= 1'b0;
			enter_debug_mode_prio_q <= 1'b0;
			load_err_q <= 1'b0;
			store_err_q <= 1'b0;
			exc_req_q <= 1'b0;
			illegal_insn_q <= 1'b0;
		end
		else begin
			ctrl_fsm_cs <= ctrl_fsm_ns;
			nmi_mode_q <= nmi_mode_d;
			do_single_step_q <= do_single_step_d;
			debug_mode_q <= debug_mode_d;
			enter_debug_mode_prio_q <= enter_debug_mode_prio_d;
			load_err_q <= load_err_d;
			store_err_q <= store_err_d;
			exc_req_q <= exc_req_d;
			illegal_insn_q <= illegal_insn_d;
		end
	end
endmodule
module ibex_if_stage (
	clk_i,
	rst_ni,
	boot_addr_i,
	req_i,
	instr_req_o,
	instr_addr_o,
	instr_gnt_i,
	instr_rvalid_i,
	instr_rdata_i,
	instr_bus_err_i,
	instr_intg_err_o,
	ic_tag_req_o,
	ic_tag_write_o,
	ic_tag_addr_o,
	ic_tag_wdata_o,
	ic_tag_rdata_i,
	ic_data_req_o,
	ic_data_write_o,
	ic_data_addr_o,
	ic_data_wdata_o,
	ic_data_rdata_i,
	ic_scr_key_valid_i,
	ic_scr_key_req_o,
	instr_valid_id_o,
	instr_new_id_o,
	instr_rdata_id_o,
	instr_rdata_alu_id_o,
	instr_rdata_c_id_o,
	instr_is_compressed_id_o,
	instr_bp_taken_o,
	instr_fetch_err_o,
	instr_fetch_err_plus2_o,
	illegal_c_insn_id_o,
	dummy_instr_id_o,
	pc_if_o,
	pc_id_o,
	pmp_err_if_i,
	pmp_err_if_plus2_i,
	instr_valid_clear_i,
	pc_set_i,
	pc_mux_i,
	nt_branch_mispredict_i,
	nt_branch_addr_i,
	exc_pc_mux_i,
	exc_cause,
	dummy_instr_en_i,
	dummy_instr_mask_i,
	dummy_instr_seed_en_i,
	dummy_instr_seed_i,
	icache_enable_i,
	icache_inval_i,
	icache_ecc_error_o,
	branch_target_ex_i,
	csr_mepc_i,
	csr_depc_i,
	csr_mtvec_i,
	csr_mtvec_init_o,
	id_in_ready_i,
	pc_mismatch_alert_o,
	if_busy_o
);
	parameter [31:0] DmHaltAddr = 32'h1a110800;
	parameter [31:0] DmExceptionAddr = 32'h1a110808;
	parameter [0:0] DummyInstructions = 1'b0;
	parameter [0:0] ICache = 1'b0;
	parameter [0:0] ICacheECC = 1'b0;
	localparam [31:0] ibex_pkg_BUS_SIZE = 32;
	parameter [31:0] BusSizeECC = ibex_pkg_BUS_SIZE;
	localparam [31:0] ibex_pkg_ADDR_W = 32;
	localparam [31:0] ibex_pkg_IC_LINE_SIZE = 64;
	localparam [31:0] ibex_pkg_IC_LINE_BYTES = 8;
	localparam [31:0] ibex_pkg_IC_NUM_WAYS = 2;
	localparam [31:0] ibex_pkg_IC_SIZE_BYTES = 4096;
	localparam [31:0] ibex_pkg_IC_NUM_LINES = (ibex_pkg_IC_SIZE_BYTES / ibex_pkg_IC_NUM_WAYS) / ibex_pkg_IC_LINE_BYTES;
	localparam [31:0] ibex_pkg_IC_INDEX_W = $clog2(ibex_pkg_IC_NUM_LINES);
	localparam [31:0] ibex_pkg_IC_LINE_W = 3;
	localparam [31:0] ibex_pkg_IC_TAG_SIZE = ((ibex_pkg_ADDR_W - ibex_pkg_IC_INDEX_W) - ibex_pkg_IC_LINE_W) + 1;
	parameter [31:0] TagSizeECC = ibex_pkg_IC_TAG_SIZE;
	parameter [31:0] LineSizeECC = ibex_pkg_IC_LINE_SIZE;
	parameter [0:0] PCIncrCheck = 1'b0;
	parameter [0:0] ResetAll = 1'b0;
	localparam signed [31:0] ibex_pkg_LfsrWidth = 32;
	localparam [31:0] ibex_pkg_RndCnstLfsrSeedDefault = 32'hac533bf4;
	parameter [31:0] RndCnstLfsrSeed = ibex_pkg_RndCnstLfsrSeedDefault;
	localparam [159:0] ibex_pkg_RndCnstLfsrPermDefault = 160'h1e35ecba467fd1b12e958152c04fa43878a8daed;
	parameter [159:0] RndCnstLfsrPerm = ibex_pkg_RndCnstLfsrPermDefault;
	parameter [0:0] BranchPredictor = 1'b0;
	parameter [0:0] MemECC = 1'b0;
	parameter [31:0] MemDataWidth = (MemECC ? 39 : 32);
	input wire clk_i;
	input wire rst_ni;
	input wire [31:0] boot_addr_i;
	input wire req_i;
	output wire instr_req_o;
	output wire [31:0] instr_addr_o;
	input wire instr_gnt_i;
	input wire instr_rvalid_i;
	input wire [MemDataWidth - 1:0] instr_rdata_i;
	input wire instr_bus_err_i;
	output wire instr_intg_err_o;
	output wire [1:0] ic_tag_req_o;
	output wire ic_tag_write_o;
	output wire [ibex_pkg_IC_INDEX_W - 1:0] ic_tag_addr_o;
	output wire [TagSizeECC - 1:0] ic_tag_wdata_o;
	input wire [(ibex_pkg_IC_NUM_WAYS * TagSizeECC) - 1:0] ic_tag_rdata_i;
	output wire [1:0] ic_data_req_o;
	output wire ic_data_write_o;
	output wire [ibex_pkg_IC_INDEX_W - 1:0] ic_data_addr_o;
	output wire [LineSizeECC - 1:0] ic_data_wdata_o;
	input wire [(ibex_pkg_IC_NUM_WAYS * LineSizeECC) - 1:0] ic_data_rdata_i;
	input wire ic_scr_key_valid_i;
	output wire ic_scr_key_req_o;
	output wire instr_valid_id_o;
	output wire instr_new_id_o;
	output reg [31:0] instr_rdata_id_o;
	output reg [31:0] instr_rdata_alu_id_o;
	output reg [15:0] instr_rdata_c_id_o;
	output reg instr_is_compressed_id_o;
	output wire instr_bp_taken_o;
	output reg instr_fetch_err_o;
	output reg instr_fetch_err_plus2_o;
	output reg illegal_c_insn_id_o;
	output reg dummy_instr_id_o;
	output wire [31:0] pc_if_o;
	output reg [31:0] pc_id_o;
	input wire pmp_err_if_i;
	input wire pmp_err_if_plus2_i;
	input wire instr_valid_clear_i;
	input wire pc_set_i;
	input wire [2:0] pc_mux_i;
	input wire nt_branch_mispredict_i;
	input wire [31:0] nt_branch_addr_i;
	input wire [1:0] exc_pc_mux_i;
	input wire [6:0] exc_cause;
	input wire dummy_instr_en_i;
	input wire [2:0] dummy_instr_mask_i;
	input wire dummy_instr_seed_en_i;
	input wire [31:0] dummy_instr_seed_i;
	input wire icache_enable_i;
	input wire icache_inval_i;
	output wire icache_ecc_error_o;
	input wire [31:0] branch_target_ex_i;
	input wire [31:0] csr_mepc_i;
	input wire [31:0] csr_depc_i;
	input wire [31:0] csr_mtvec_i;
	output wire csr_mtvec_init_o;
	input wire id_in_ready_i;
	output wire pc_mismatch_alert_o;
	output wire if_busy_o;
	wire instr_valid_id_d;
	reg instr_valid_id_q;
	wire instr_new_id_d;
	reg instr_new_id_q;
	wire instr_err;
	wire instr_intg_err;
	wire prefetch_busy;
	wire branch_req;
	reg [31:0] fetch_addr_n;
	wire unused_fetch_addr_n0;
	wire prefetch_branch;
	wire [31:0] prefetch_addr;
	wire fetch_valid_raw;
	wire fetch_valid;
	wire fetch_ready;
	wire [31:0] fetch_rdata;
	wire [31:0] fetch_addr;
	wire fetch_err;
	wire fetch_err_plus2;
	wire [31:0] instr_decompressed;
	wire illegal_c_insn;
	wire instr_is_compressed;
	wire if_instr_valid;
	wire [31:0] if_instr_rdata;
	wire [31:0] if_instr_addr;
	wire if_instr_bus_err;
	wire if_instr_pmp_err;
	wire if_instr_err;
	wire if_instr_err_plus2;
	reg [31:0] exc_pc;
	wire if_id_pipe_reg_we;
	wire stall_dummy_instr;
	wire [31:0] instr_out;
	wire instr_is_compressed_out;
	wire illegal_c_instr_out;
	wire instr_err_out;
	wire predict_branch_taken;
	wire [31:0] predict_branch_pc;
	reg [4:0] irq_vec;
	wire [2:0] pc_mux_internal;
	wire [7:0] unused_boot_addr;
	wire [7:0] unused_csr_mtvec;
	wire unused_exc_cause;
	assign unused_boot_addr = boot_addr_i[7:0];
	assign unused_csr_mtvec = csr_mtvec_i[7:0];
	assign unused_exc_cause = |{exc_cause[5], exc_cause[6]};
	localparam [6:0] ibex_pkg_ExcCauseIrqNm = 7'h3f;
	always @(*) begin : exc_pc_mux
		irq_vec = exc_cause[4-:5];
		if (exc_cause[6])
			irq_vec = ibex_pkg_ExcCauseIrqNm[4-:5];
		case (exc_pc_mux_i)
			2'd0: exc_pc = {csr_mtvec_i[31:8], 8'h00};
			2'd1: exc_pc = {csr_mtvec_i[31:8], 1'b0, irq_vec, 2'b00};
			2'd2: exc_pc = DmHaltAddr;
			2'd3: exc_pc = DmExceptionAddr;
			default: exc_pc = {csr_mtvec_i[31:8], 8'h00};
		endcase
	end
	assign pc_mux_internal = ((BranchPredictor && predict_branch_taken) && !pc_set_i ? 3'd5 : pc_mux_i);
	always @(*) begin : fetch_addr_mux
		case (pc_mux_internal)
			3'd0: fetch_addr_n = {boot_addr_i[31:8], 8'h80};
			3'd1: fetch_addr_n = branch_target_ex_i;
			3'd2: fetch_addr_n = exc_pc;
			3'd3: fetch_addr_n = csr_mepc_i;
			3'd4: fetch_addr_n = csr_depc_i;
			3'd5: fetch_addr_n = (BranchPredictor ? predict_branch_pc : {boot_addr_i[31:8], 8'h80});
			default: fetch_addr_n = {boot_addr_i[31:8], 8'h80};
		endcase
	end
	assign csr_mtvec_init_o = (pc_mux_i == 3'd0) & pc_set_i;
	generate
		if (MemECC) begin : g_mem_ecc
			wire [1:0] ecc_err;
			wire [MemDataWidth - 1:0] instr_rdata_buf;
			prim_buf #(.Width(MemDataWidth)) u_prim_buf_instr_rdata(
				.in_i(instr_rdata_i),
				.out_o(instr_rdata_buf)
			);
			prim_secded_inv_39_32_dec u_instr_intg_dec(
				.data_i(instr_rdata_buf),
				.data_o(),
				.syndrome_o(),
				.err_o(ecc_err)
			);
			assign instr_intg_err = |ecc_err;
		end
		else begin : g_no_mem_ecc
			assign instr_intg_err = 1'b0;
		end
	endgenerate
	assign instr_err = instr_intg_err | instr_bus_err_i;
	assign instr_intg_err_o = instr_intg_err & instr_rvalid_i;
	assign prefetch_branch = branch_req | nt_branch_mispredict_i;
	assign prefetch_addr = (branch_req ? {fetch_addr_n[31:1], 1'b0} : nt_branch_addr_i);
	assign fetch_valid = fetch_valid_raw & ~nt_branch_mispredict_i;
	generate
		if (ICache) begin : gen_icache
			ibex_icache #(
				.ICacheECC(ICacheECC),
				.ResetAll(ResetAll),
				.BusSizeECC(BusSizeECC),
				.TagSizeECC(TagSizeECC),
				.LineSizeECC(LineSizeECC)
			) icache_i(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.req_i(req_i),
				.branch_i(prefetch_branch),
				.addr_i(prefetch_addr),
				.ready_i(fetch_ready),
				.valid_o(fetch_valid_raw),
				.rdata_o(fetch_rdata),
				.addr_o(fetch_addr),
				.err_o(fetch_err),
				.err_plus2_o(fetch_err_plus2),
				.instr_req_o(instr_req_o),
				.instr_addr_o(instr_addr_o),
				.instr_gnt_i(instr_gnt_i),
				.instr_rvalid_i(instr_rvalid_i),
				.instr_rdata_i(instr_rdata_i[31:0]),
				.instr_err_i(instr_err),
				.ic_tag_req_o(ic_tag_req_o),
				.ic_tag_write_o(ic_tag_write_o),
				.ic_tag_addr_o(ic_tag_addr_o),
				.ic_tag_wdata_o(ic_tag_wdata_o),
				.ic_tag_rdata_i(ic_tag_rdata_i),
				.ic_data_req_o(ic_data_req_o),
				.ic_data_write_o(ic_data_write_o),
				.ic_data_addr_o(ic_data_addr_o),
				.ic_data_wdata_o(ic_data_wdata_o),
				.ic_data_rdata_i(ic_data_rdata_i),
				.ic_scr_key_valid_i(ic_scr_key_valid_i),
				.ic_scr_key_req_o(ic_scr_key_req_o),
				.icache_enable_i(icache_enable_i),
				.icache_inval_i(icache_inval_i),
				.busy_o(prefetch_busy),
				.ecc_error_o(icache_ecc_error_o)
			);
		end
		else begin : gen_prefetch_buffer
			ibex_prefetch_buffer #(.ResetAll(ResetAll)) prefetch_buffer_i(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.req_i(req_i),
				.branch_i(prefetch_branch),
				.addr_i(prefetch_addr),
				.ready_i(fetch_ready),
				.valid_o(fetch_valid_raw),
				.rdata_o(fetch_rdata),
				.addr_o(fetch_addr),
				.err_o(fetch_err),
				.err_plus2_o(fetch_err_plus2),
				.instr_req_o(instr_req_o),
				.instr_addr_o(instr_addr_o),
				.instr_gnt_i(instr_gnt_i),
				.instr_rvalid_i(instr_rvalid_i),
				.instr_rdata_i(instr_rdata_i[31:0]),
				.instr_err_i(instr_err),
				.busy_o(prefetch_busy)
			);
			wire unused_icen;
			wire unused_icinv;
			wire unused_scr_key_valid;
			wire [(ibex_pkg_IC_NUM_WAYS * TagSizeECC) - 1:0] unused_tag_ram_input;
			wire [(ibex_pkg_IC_NUM_WAYS * LineSizeECC) - 1:0] unused_data_ram_input;
			assign unused_icen = icache_enable_i;
			assign unused_icinv = icache_inval_i;
			assign unused_tag_ram_input = ic_tag_rdata_i;
			assign unused_data_ram_input = ic_data_rdata_i;
			assign unused_scr_key_valid = ic_scr_key_valid_i;
			assign ic_tag_req_o = 'b0;
			assign ic_tag_write_o = 'b0;
			assign ic_tag_addr_o = 'b0;
			assign ic_tag_wdata_o = 'b0;
			assign ic_data_req_o = 'b0;
			assign ic_data_write_o = 'b0;
			assign ic_data_addr_o = 'b0;
			assign ic_data_wdata_o = 'b0;
			assign ic_scr_key_req_o = 'b0;
			assign icache_ecc_error_o = 'b0;
		end
	endgenerate
	assign unused_fetch_addr_n0 = fetch_addr_n[0];
	assign branch_req = pc_set_i | predict_branch_taken;
	assign pc_if_o = if_instr_addr;
	assign if_busy_o = prefetch_busy;
	assign if_instr_pmp_err = pmp_err_if_i | ((if_instr_addr[1] & ~instr_is_compressed) & pmp_err_if_plus2_i);
	assign if_instr_err = if_instr_bus_err | if_instr_pmp_err;
	assign if_instr_err_plus2 = (((if_instr_addr[1] & ~instr_is_compressed) & pmp_err_if_plus2_i) | fetch_err_plus2) & ~pmp_err_if_i;
	ibex_compressed_decoder compressed_decoder_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.valid_i(fetch_valid & ~fetch_err),
		.instr_i(if_instr_rdata),
		.instr_o(instr_decompressed),
		.is_compressed_o(instr_is_compressed),
		.illegal_instr_o(illegal_c_insn)
	);
	generate
		if (DummyInstructions) begin : gen_dummy_instr
			wire insert_dummy_instr;
			wire [31:0] dummy_instr_data;
			ibex_dummy_instr #(
				.RndCnstLfsrSeed(RndCnstLfsrSeed),
				.RndCnstLfsrPerm(RndCnstLfsrPerm)
			) dummy_instr_i(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.dummy_instr_en_i(dummy_instr_en_i),
				.dummy_instr_mask_i(dummy_instr_mask_i),
				.dummy_instr_seed_en_i(dummy_instr_seed_en_i),
				.dummy_instr_seed_i(dummy_instr_seed_i),
				.fetch_valid_i(fetch_valid),
				.id_in_ready_i(id_in_ready_i),
				.insert_dummy_instr_o(insert_dummy_instr),
				.dummy_instr_data_o(dummy_instr_data)
			);
			assign instr_out = (insert_dummy_instr ? dummy_instr_data : instr_decompressed);
			assign instr_is_compressed_out = (insert_dummy_instr ? 1'b0 : instr_is_compressed);
			assign illegal_c_instr_out = (insert_dummy_instr ? 1'b0 : illegal_c_insn);
			assign instr_err_out = (insert_dummy_instr ? 1'b0 : if_instr_err);
			assign stall_dummy_instr = insert_dummy_instr;
			always @(posedge clk_i)
				if (!rst_ni)
					dummy_instr_id_o <= 1'b0;
				else if (if_id_pipe_reg_we)
					dummy_instr_id_o <= insert_dummy_instr;
		end
		else begin : gen_no_dummy_instr
			wire unused_dummy_en;
			wire [2:0] unused_dummy_mask;
			wire unused_dummy_seed_en;
			wire [31:0] unused_dummy_seed;
			assign unused_dummy_en = dummy_instr_en_i;
			assign unused_dummy_mask = dummy_instr_mask_i;
			assign unused_dummy_seed_en = dummy_instr_seed_en_i;
			assign unused_dummy_seed = dummy_instr_seed_i;
			assign instr_out = instr_decompressed;
			assign instr_is_compressed_out = instr_is_compressed;
			assign illegal_c_instr_out = illegal_c_insn;
			assign instr_err_out = if_instr_err;
			assign stall_dummy_instr = 1'b0;
			wire [1:1] sv2v_tmp_A80D7;
			assign sv2v_tmp_A80D7 = 1'b0;
			always @(*) dummy_instr_id_o = sv2v_tmp_A80D7;
		end
	endgenerate
	assign instr_valid_id_d = ((if_instr_valid & id_in_ready_i) & ~pc_set_i) | (instr_valid_id_q & ~instr_valid_clear_i);
	assign instr_new_id_d = if_instr_valid & id_in_ready_i;
	always @(posedge clk_i)
		if (!rst_ni) begin
			instr_valid_id_q <= 1'b0;
			instr_new_id_q <= 1'b0;
		end
		else begin
			instr_valid_id_q <= instr_valid_id_d;
			instr_new_id_q <= instr_new_id_d;
		end
	assign instr_valid_id_o = instr_valid_id_q;
	assign instr_new_id_o = instr_new_id_q;
	assign if_id_pipe_reg_we = instr_new_id_d;
	generate
		if (ResetAll) begin : g_instr_rdata_ra
			always @(posedge clk_i)
				if (!rst_ni) begin
					instr_rdata_id_o <= 1'sb0;
					instr_rdata_alu_id_o <= 1'sb0;
					instr_fetch_err_o <= 1'sb0;
					instr_fetch_err_plus2_o <= 1'sb0;
					instr_rdata_c_id_o <= 1'sb0;
					instr_is_compressed_id_o <= 1'sb0;
					illegal_c_insn_id_o <= 1'sb0;
					pc_id_o <= 1'sb0;
				end
				else if (if_id_pipe_reg_we) begin
					instr_rdata_id_o <= instr_out;
					instr_rdata_alu_id_o <= instr_out;
					instr_fetch_err_o <= instr_err_out;
					instr_fetch_err_plus2_o <= if_instr_err_plus2;
					instr_rdata_c_id_o <= if_instr_rdata[15:0];
					instr_is_compressed_id_o <= instr_is_compressed_out;
					illegal_c_insn_id_o <= illegal_c_instr_out;
					pc_id_o <= pc_if_o;
				end
		end
		else begin : g_instr_rdata_nr
			always @(posedge clk_i)
				if (if_id_pipe_reg_we) begin
					instr_rdata_id_o <= instr_out;
					instr_rdata_alu_id_o <= instr_out;
					instr_fetch_err_o <= instr_err_out;
					instr_fetch_err_plus2_o <= if_instr_err_plus2;
					instr_rdata_c_id_o <= if_instr_rdata[15:0];
					instr_is_compressed_id_o <= instr_is_compressed_out;
					illegal_c_insn_id_o <= illegal_c_instr_out;
					pc_id_o <= pc_if_o;
				end
		end
		if (PCIncrCheck) begin : g_secure_pc
			wire [31:0] prev_instr_addr_incr;
			wire [31:0] prev_instr_addr_incr_buf;
			reg prev_instr_seq_q;
			wire prev_instr_seq_d;
			assign prev_instr_seq_d = (((prev_instr_seq_q | instr_new_id_d) & ~branch_req) & ~if_instr_err) & ~stall_dummy_instr;
			always @(posedge clk_i)
				if (!rst_ni)
					prev_instr_seq_q <= 1'b0;
				else
					prev_instr_seq_q <= prev_instr_seq_d;
			assign prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd2 : 32'd4);
			prim_buf #(.Width(32)) u_prev_instr_addr_incr_buf(
				.in_i(prev_instr_addr_incr),
				.out_o(prev_instr_addr_incr_buf)
			);
			assign pc_mismatch_alert_o = prev_instr_seq_q & (pc_if_o != prev_instr_addr_incr_buf);
		end
		else begin : g_no_secure_pc
			assign pc_mismatch_alert_o = 1'b0;
		end
		if (BranchPredictor) begin : g_branch_predictor
			reg [31:0] instr_skid_data_q;
			reg [31:0] instr_skid_addr_q;
			reg instr_skid_bp_taken_q;
			reg instr_skid_valid_q;
			wire instr_skid_valid_d;
			wire instr_skid_en;
			reg instr_bp_taken_q;
			wire instr_bp_taken_d;
			wire predict_branch_taken_raw;
			if (ResetAll) begin : g_bp_taken_ra
				always @(posedge clk_i)
					if (!rst_ni)
						instr_bp_taken_q <= 1'sb0;
					else if (if_id_pipe_reg_we)
						instr_bp_taken_q <= instr_bp_taken_d;
			end
			else begin : g_bp_taken_nr
				always @(posedge clk_i)
					if (if_id_pipe_reg_we)
						instr_bp_taken_q <= instr_bp_taken_d;
			end
			assign instr_skid_en = ((predict_branch_taken & ~pc_set_i) & ~id_in_ready_i) & ~instr_skid_valid_q;
			assign instr_skid_valid_d = ((instr_skid_valid_q & ~id_in_ready_i) & ~stall_dummy_instr) | instr_skid_en;
			always @(posedge clk_i)
				if (!rst_ni)
					instr_skid_valid_q <= 1'b0;
				else
					instr_skid_valid_q <= instr_skid_valid_d;
			if (ResetAll) begin : g_instr_skid_ra
				always @(posedge clk_i)
					if (!rst_ni) begin
						instr_skid_bp_taken_q <= 1'sb0;
						instr_skid_data_q <= 1'sb0;
						instr_skid_addr_q <= 1'sb0;
					end
					else if (instr_skid_en) begin
						instr_skid_bp_taken_q <= predict_branch_taken;
						instr_skid_data_q <= fetch_rdata;
						instr_skid_addr_q <= fetch_addr;
					end
			end
			else begin : g_instr_skid_nr
				always @(posedge clk_i)
					if (instr_skid_en) begin
						instr_skid_bp_taken_q <= predict_branch_taken;
						instr_skid_data_q <= fetch_rdata;
						instr_skid_addr_q <= fetch_addr;
					end
			end
			ibex_branch_predict branch_predict_i(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.fetch_rdata_i(fetch_rdata),
				.fetch_pc_i(fetch_addr),
				.fetch_valid_i(fetch_valid),
				.predict_branch_taken_o(predict_branch_taken_raw),
				.predict_branch_pc_o(predict_branch_pc)
			);
			assign predict_branch_taken = (predict_branch_taken_raw & ~instr_skid_valid_q) & ~fetch_err;
			assign if_instr_valid = fetch_valid | (instr_skid_valid_q & ~nt_branch_mispredict_i);
			assign if_instr_rdata = (instr_skid_valid_q ? instr_skid_data_q : fetch_rdata);
			assign if_instr_addr = (instr_skid_valid_q ? instr_skid_addr_q : fetch_addr);
			assign if_instr_bus_err = ~instr_skid_valid_q & fetch_err;
			assign instr_bp_taken_d = (instr_skid_valid_q ? instr_skid_bp_taken_q : predict_branch_taken);
			assign fetch_ready = (id_in_ready_i & ~stall_dummy_instr) & ~instr_skid_valid_q;
			assign instr_bp_taken_o = instr_bp_taken_q;
		end
		else begin : g_no_branch_predictor
			assign instr_bp_taken_o = 1'b0;
			assign predict_branch_taken = 1'b0;
			assign predict_branch_pc = 32'b00000000000000000000000000000000;
			assign if_instr_valid = fetch_valid;
			assign if_instr_rdata = fetch_rdata;
			assign if_instr_addr = fetch_addr;
			assign if_instr_bus_err = fetch_err;
			assign fetch_ready = id_in_ready_i & ~stall_dummy_instr;
		end
	endgenerate
endmodule
module ibex_pmp (
	csr_pmp_cfg_i,
	csr_pmp_addr_i,
	csr_pmp_mseccfg_i,
	priv_mode_i,
	pmp_req_addr_i,
	pmp_req_type_i,
	pmp_req_err_o
);
	parameter [31:0] PMPGranularity = 0;
	parameter [31:0] PMPNumChan = 2;
	parameter [31:0] PMPNumRegions = 4;
	input wire [(PMPNumRegions * 6) - 1:0] csr_pmp_cfg_i;
	input wire [(PMPNumRegions * 34) - 1:0] csr_pmp_addr_i;
	input wire [2:0] csr_pmp_mseccfg_i;
	input wire [(PMPNumChan * 2) - 1:0] priv_mode_i;
	input wire [(PMPNumChan * 34) - 1:0] pmp_req_addr_i;
	input wire [(PMPNumChan * 2) - 1:0] pmp_req_type_i;
	output wire [0:PMPNumChan - 1] pmp_req_err_o;
	wire [33:0] region_start_addr [0:PMPNumRegions - 1];
	wire [33:PMPGranularity + 2] region_addr_mask [0:PMPNumRegions - 1];
	wire [(PMPNumChan * PMPNumRegions) - 1:0] region_match_gt;
	wire [(PMPNumChan * PMPNumRegions) - 1:0] region_match_lt;
	wire [(PMPNumChan * PMPNumRegions) - 1:0] region_match_eq;
	reg [(PMPNumChan * PMPNumRegions) - 1:0] region_match_all;
	wire [(PMPNumChan * PMPNumRegions) - 1:0] region_basic_perm_check;
	wire [(PMPNumChan * PMPNumRegions) - 1:0] region_perm_check;
	function automatic mml_perm_check;
		input reg [5:0] csr_pmp_cfg;
		input reg [1:0] pmp_req_type;
		input reg [1:0] priv_mode;
		input reg permission_check;
		reg result;
		reg unused_cfg;
		begin
			result = 1'b0;
			unused_cfg = |csr_pmp_cfg[4-:2];
			if (!csr_pmp_cfg[0] && csr_pmp_cfg[1])
				case ({csr_pmp_cfg[5], csr_pmp_cfg[2]})
					2'b00: result = (pmp_req_type == 2'b10) | ((pmp_req_type == 2'b01) & (priv_mode == 2'b11));
					2'b01: result = (pmp_req_type == 2'b10) | (pmp_req_type == 2'b01);
					2'b10: result = pmp_req_type == 2'b00;
					2'b11: result = (pmp_req_type == 2'b00) | ((pmp_req_type == 2'b10) & (priv_mode == 2'b11));
					default:
						;
				endcase
			else if (((csr_pmp_cfg[0] & csr_pmp_cfg[1]) & csr_pmp_cfg[2]) & csr_pmp_cfg[5])
				result = pmp_req_type == 2'b10;
			else
				result = permission_check & (priv_mode == 2'b11 ? csr_pmp_cfg[5] : ~csr_pmp_cfg[5]);
			mml_perm_check = result;
		end
	endfunction
	function automatic orig_perm_check;
		input reg pmp_cfg_lock;
		input reg [1:0] priv_mode;
		input reg permission_check;
		orig_perm_check = (priv_mode == 2'b11 ? ~pmp_cfg_lock | permission_check : permission_check);
	endfunction
	function automatic perm_check_wrapper;
		input reg csr_pmp_mseccfg_mml;
		input reg [5:0] csr_pmp_cfg;
		input reg [1:0] pmp_req_type;
		input reg [1:0] priv_mode;
		input reg permission_check;
		perm_check_wrapper = (csr_pmp_mseccfg_mml ? mml_perm_check(csr_pmp_cfg, pmp_req_type, priv_mode, permission_check) : orig_perm_check(csr_pmp_cfg[5], priv_mode, permission_check));
	endfunction
	function automatic access_fault_check;
		input reg csr_pmp_mseccfg_mmwp;
		input reg csr_pmp_mseccfg_mml;
		input reg [1:0] pmp_req_type;
		input reg [PMPNumRegions - 1:0] match_all;
		input reg [1:0] priv_mode;
		input reg [PMPNumRegions - 1:0] final_perm_check;
		reg access_fail;
		reg matched;
		begin
			access_fail = (csr_pmp_mseccfg_mmwp | (priv_mode != 2'b11)) | (csr_pmp_mseccfg_mml && (pmp_req_type == 2'b00));
			matched = 1'b0;
			begin : sv2v_autoblock_1
				reg signed [31:0] r;
				for (r = 0; r < PMPNumRegions; r = r + 1)
					if (!matched && match_all[r]) begin
						access_fail = ~final_perm_check[r];
						matched = 1'b1;
					end
			end
			access_fault_check = access_fail;
		end
	endfunction
	genvar r;
	generate
		for (r = 0; r < PMPNumRegions; r = r + 1) begin : g_addr_exp
			if (r == 0) begin : g_entry0
				assign region_start_addr[r] = (csr_pmp_cfg_i[(((PMPNumRegions - 1) - r) * 6) + 4-:2] == 2'b01 ? 34'h000000000 : csr_pmp_addr_i[((PMPNumRegions - 1) - r) * 34+:34]);
			end
			else begin : g_oth
				assign region_start_addr[r] = (csr_pmp_cfg_i[(((PMPNumRegions - 1) - r) * 6) + 4-:2] == 2'b01 ? csr_pmp_addr_i[((PMPNumRegions - 1) - (r - 1)) * 34+:34] : csr_pmp_addr_i[((PMPNumRegions - 1) - r) * 34+:34]);
			end
			genvar b;
			for (b = PMPGranularity + 2; b < 34; b = b + 1) begin : g_bitmask
				if (b == 2) begin : g_bit0
					assign region_addr_mask[r][b] = csr_pmp_cfg_i[(((PMPNumRegions - 1) - r) * 6) + 4-:2] != 2'b11;
				end
				else begin : g_others
					if (PMPGranularity == 0) begin : g_region_addr_mask_zero_granularity
						assign region_addr_mask[r][b] = (csr_pmp_cfg_i[(((PMPNumRegions - 1) - r) * 6) + 4-:2] != 2'b11) | ~&csr_pmp_addr_i[(((PMPNumRegions - 1) - r) * 34) + ((b - 1) >= 2 ? b - 1 : ((b - 1) + ((b - 1) >= 2 ? b - 2 : 4 - b)) - 1)-:((b - 1) >= 2 ? b - 2 : 4 - b)];
					end
					else begin : g_region_addr_mask_other_granularity
						assign region_addr_mask[r][b] = (csr_pmp_cfg_i[(((PMPNumRegions - 1) - r) * 6) + 4-:2] != 2'b11) | ~&csr_pmp_addr_i[(((PMPNumRegions - 1) - r) * 34) + ((b - 1) >= (PMPGranularity + 1) ? b - 1 : ((b - 1) + ((b - 1) >= (PMPGranularity + 1) ? ((b - 1) - (PMPGranularity + 1)) + 1 : ((PMPGranularity + 1) - (b - 1)) + 1)) - 1)-:((b - 1) >= (PMPGranularity + 1) ? ((b - 1) - (PMPGranularity + 1)) + 1 : ((PMPGranularity + 1) - (b - 1)) + 1)];
					end
				end
			end
		end
	endgenerate
	genvar c;
	generate
		for (c = 0; c < PMPNumChan; c = c + 1) begin : g_access_check
			genvar r;
			for (r = 0; r < PMPNumRegions; r = r + 1) begin : g_regions
				assign region_match_eq[(c * PMPNumRegions) + r] = (pmp_req_addr_i[(((PMPNumChan - 1) - c) * 34) + (33 >= (PMPGranularity + 2) ? 33 : (33 + (33 >= (PMPGranularity + 2) ? 34 - (PMPGranularity + 2) : PMPGranularity - 30)) - 1)-:(33 >= (PMPGranularity + 2) ? 34 - (PMPGranularity + 2) : PMPGranularity - 30)] & region_addr_mask[r]) == (region_start_addr[r][33:PMPGranularity + 2] & region_addr_mask[r]);
				assign region_match_gt[(c * PMPNumRegions) + r] = pmp_req_addr_i[(((PMPNumChan - 1) - c) * 34) + (33 >= (PMPGranularity + 2) ? 33 : (33 + (33 >= (PMPGranularity + 2) ? 34 - (PMPGranularity + 2) : PMPGranularity - 30)) - 1)-:(33 >= (PMPGranularity + 2) ? 34 - (PMPGranularity + 2) : PMPGranularity - 30)] > region_start_addr[r][33:PMPGranularity + 2];
				assign region_match_lt[(c * PMPNumRegions) + r] = pmp_req_addr_i[(((PMPNumChan - 1) - c) * 34) + (33 >= (PMPGranularity + 2) ? 33 : (33 + (33 >= (PMPGranularity + 2) ? 34 - (PMPGranularity + 2) : PMPGranularity - 30)) - 1)-:(33 >= (PMPGranularity + 2) ? 34 - (PMPGranularity + 2) : PMPGranularity - 30)] < csr_pmp_addr_i[(((PMPNumRegions - 1) - r) * 34) + (33 >= (PMPGranularity + 2) ? 33 : (33 + (33 >= (PMPGranularity + 2) ? 34 - (PMPGranularity + 2) : PMPGranularity - 30)) - 1)-:(33 >= (PMPGranularity + 2) ? 34 - (PMPGranularity + 2) : PMPGranularity - 30)];
				always @(*) begin
					region_match_all[(c * PMPNumRegions) + r] = 1'b0;
					case (csr_pmp_cfg_i[(((PMPNumRegions - 1) - r) * 6) + 4-:2])
						2'b00: region_match_all[(c * PMPNumRegions) + r] = 1'b0;
						2'b10: region_match_all[(c * PMPNumRegions) + r] = region_match_eq[(c * PMPNumRegions) + r];
						2'b11: region_match_all[(c * PMPNumRegions) + r] = region_match_eq[(c * PMPNumRegions) + r];
						2'b01: region_match_all[(c * PMPNumRegions) + r] = (region_match_eq[(c * PMPNumRegions) + r] | region_match_gt[(c * PMPNumRegions) + r]) & region_match_lt[(c * PMPNumRegions) + r];
						default: region_match_all[(c * PMPNumRegions) + r] = 1'b0;
					endcase
				end
				assign region_basic_perm_check[(c * PMPNumRegions) + r] = (((pmp_req_type_i[((PMPNumChan - 1) - c) * 2+:2] == 2'b00) & csr_pmp_cfg_i[(((PMPNumRegions - 1) - r) * 6) + 2]) | ((pmp_req_type_i[((PMPNumChan - 1) - c) * 2+:2] == 2'b01) & csr_pmp_cfg_i[(((PMPNumRegions - 1) - r) * 6) + 1])) | ((pmp_req_type_i[((PMPNumChan - 1) - c) * 2+:2] == 2'b10) & csr_pmp_cfg_i[((PMPNumRegions - 1) - r) * 6]);
				assign region_perm_check[(c * PMPNumRegions) + r] = perm_check_wrapper(csr_pmp_mseccfg_i[0], csr_pmp_cfg_i[((PMPNumRegions - 1) - r) * 6+:6], pmp_req_type_i[((PMPNumChan - 1) - c) * 2+:2], priv_mode_i[((PMPNumChan - 1) - c) * 2+:2], region_basic_perm_check[(c * PMPNumRegions) + r]);
				wire unused_sigs;
				assign unused_sigs = ^{region_start_addr[r][PMPGranularity + 1:0], pmp_req_addr_i[(((PMPNumChan - 1) - c) * 34) + ((PMPGranularity + 1) >= 0 ? PMPGranularity + 1 : ((PMPGranularity + 1) + ((PMPGranularity + 1) >= 0 ? PMPGranularity + 2 : 1 - (PMPGranularity + 1))) - 1)-:((PMPGranularity + 1) >= 0 ? PMPGranularity + 2 : 1 - (PMPGranularity + 1))]};
			end
			assign pmp_req_err_o[c] = access_fault_check(csr_pmp_mseccfg_i[1], csr_pmp_mseccfg_i[0], pmp_req_type_i[((PMPNumChan - 1) - c) * 2+:2], region_match_all[c * PMPNumRegions+:PMPNumRegions], priv_mode_i[((PMPNumChan - 1) - c) * 2+:2], region_perm_check[c * PMPNumRegions+:PMPNumRegions]);
		end
	endgenerate
	wire unused_csr_pmp_mseccfg_rlb;
	assign unused_csr_pmp_mseccfg_rlb = csr_pmp_mseccfg_i[2];
endmodule
module prim_buf (
	in_i,
	out_o
);
	parameter signed [31:0] Width = 1;
	input [Width - 1:0] in_i;
	output wire [Width - 1:0] out_o;
	generate
		if (1) begin : gen_generic
			prim_generic_buf #(.Width(Width)) u_impl_generic(
				.in_i(in_i),
				.out_o(out_o)
			);
		end
	endgenerate
endmodule
module ibex_load_store_unit (
	clk_i,
	rst_ni,
	data_req_o,
	data_gnt_i,
	data_rvalid_i,
	data_bus_err_i,
	data_pmp_err_i,
	data_addr_o,
	data_we_o,
	data_be_o,
	data_wdata_o,
	data_rdata_i,
	lsu_we_i,
	lsu_type_i,
	lsu_wdata_i,
	lsu_sign_ext_i,
	lsu_rdata_o,
	lsu_rdata_valid_o,
	lsu_req_i,
	adder_result_ex_i,
	addr_incr_req_o,
	addr_last_o,
	lsu_req_done_o,
	lsu_resp_valid_o,
	load_err_o,
	load_resp_intg_err_o,
	store_err_o,
	store_resp_intg_err_o,
	busy_o,
	perf_load_o,
	perf_store_o
);
	parameter [0:0] MemECC = 1'b0;
	parameter [31:0] MemDataWidth = (MemECC ? 39 : 32);
	input wire clk_i;
	input wire rst_ni;
	output reg data_req_o;
	input wire data_gnt_i;
	input wire data_rvalid_i;
	input wire data_bus_err_i;
	input wire data_pmp_err_i;
	output wire [31:0] data_addr_o;
	output wire data_we_o;
	output wire [3:0] data_be_o;
	output wire [MemDataWidth - 1:0] data_wdata_o;
	input wire [MemDataWidth - 1:0] data_rdata_i;
	input wire lsu_we_i;
	input wire [1:0] lsu_type_i;
	input wire [31:0] lsu_wdata_i;
	input wire lsu_sign_ext_i;
	output wire [31:0] lsu_rdata_o;
	output wire lsu_rdata_valid_o;
	input wire lsu_req_i;
	input wire [31:0] adder_result_ex_i;
	output reg addr_incr_req_o;
	output wire [31:0] addr_last_o;
	output wire lsu_req_done_o;
	output wire lsu_resp_valid_o;
	output wire load_err_o;
	output wire load_resp_intg_err_o;
	output wire store_err_o;
	output wire store_resp_intg_err_o;
	output wire busy_o;
	output reg perf_load_o;
	output reg perf_store_o;
	wire [31:0] data_addr;
	wire [31:0] data_addr_w_aligned;
	reg [31:0] addr_last_q;
	wire [31:0] addr_last_d;
	reg addr_update;
	reg ctrl_update;
	reg rdata_update;
	reg [31:8] rdata_q;
	reg [1:0] rdata_offset_q;
	reg [1:0] data_type_q;
	reg data_sign_ext_q;
	reg data_we_q;
	wire [1:0] data_offset;
	reg [3:0] data_be;
	reg [31:0] data_wdata;
	reg [31:0] data_rdata_ext;
	reg [31:0] rdata_w_ext;
	reg [31:0] rdata_h_ext;
	reg [31:0] rdata_b_ext;
	wire split_misaligned_access;
	reg handle_misaligned_q;
	reg handle_misaligned_d;
	reg pmp_err_q;
	reg pmp_err_d;
	reg lsu_err_q;
	reg lsu_err_d;
	wire data_intg_err;
	wire data_or_pmp_err;
	reg [2:0] ls_fsm_cs;
	reg [2:0] ls_fsm_ns;
	assign data_addr = adder_result_ex_i;
	assign data_offset = data_addr[1:0];
	always @(*)
		case (lsu_type_i)
			2'b00:
				if (!handle_misaligned_q)
					case (data_offset)
						2'b00: data_be = 4'b1111;
						2'b01: data_be = 4'b1110;
						2'b10: data_be = 4'b1100;
						2'b11: data_be = 4'b1000;
						default: data_be = 4'b1111;
					endcase
				else
					case (data_offset)
						2'b00: data_be = 4'b0000;
						2'b01: data_be = 4'b0001;
						2'b10: data_be = 4'b0011;
						2'b11: data_be = 4'b0111;
						default: data_be = 4'b1111;
					endcase
			2'b01:
				if (!handle_misaligned_q)
					case (data_offset)
						2'b00: data_be = 4'b0011;
						2'b01: data_be = 4'b0110;
						2'b10: data_be = 4'b1100;
						2'b11: data_be = 4'b1000;
						default: data_be = 4'b1111;
					endcase
				else
					data_be = 4'b0001;
			2'b10, 2'b11:
				case (data_offset)
					2'b00: data_be = 4'b0001;
					2'b01: data_be = 4'b0010;
					2'b10: data_be = 4'b0100;
					2'b11: data_be = 4'b1000;
					default: data_be = 4'b1111;
				endcase
			default: data_be = 4'b1111;
		endcase
	always @(*)
		case (data_offset)
			2'b00: data_wdata = lsu_wdata_i[31:0];
			2'b01: data_wdata = {lsu_wdata_i[23:0], lsu_wdata_i[31:24]};
			2'b10: data_wdata = {lsu_wdata_i[15:0], lsu_wdata_i[31:16]};
			2'b11: data_wdata = {lsu_wdata_i[7:0], lsu_wdata_i[31:8]};
			default: data_wdata = lsu_wdata_i[31:0];
		endcase
	always @(posedge clk_i)
		if (!rst_ni)
			rdata_q <= 1'sb0;
		else if (rdata_update)
			rdata_q <= data_rdata_i[31:8];
	always @(posedge clk_i)
		if (!rst_ni) begin
			rdata_offset_q <= 2'h0;
			data_type_q <= 2'h0;
			data_sign_ext_q <= 1'b0;
			data_we_q <= 1'b0;
		end
		else if (ctrl_update) begin
			rdata_offset_q <= data_offset;
			data_type_q <= lsu_type_i;
			data_sign_ext_q <= lsu_sign_ext_i;
			data_we_q <= lsu_we_i;
		end
	assign addr_last_d = (addr_incr_req_o ? data_addr_w_aligned : data_addr);
	always @(posedge clk_i)
		if (!rst_ni)
			addr_last_q <= 1'sb0;
		else if (addr_update)
			addr_last_q <= addr_last_d;
	always @(*)
		case (rdata_offset_q)
			2'b00: rdata_w_ext = data_rdata_i[31:0];
			2'b01: rdata_w_ext = {data_rdata_i[7:0], rdata_q[31:8]};
			2'b10: rdata_w_ext = {data_rdata_i[15:0], rdata_q[31:16]};
			2'b11: rdata_w_ext = {data_rdata_i[23:0], rdata_q[31:24]};
			default: rdata_w_ext = data_rdata_i[31:0];
		endcase
	always @(*)
		case (rdata_offset_q)
			2'b00:
				if (!data_sign_ext_q)
					rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
				else
					rdata_h_ext = {{16 {data_rdata_i[15]}}, data_rdata_i[15:0]};
			2'b01:
				if (!data_sign_ext_q)
					rdata_h_ext = {16'h0000, data_rdata_i[23:8]};
				else
					rdata_h_ext = {{16 {data_rdata_i[23]}}, data_rdata_i[23:8]};
			2'b10:
				if (!data_sign_ext_q)
					rdata_h_ext = {16'h0000, data_rdata_i[31:16]};
				else
					rdata_h_ext = {{16 {data_rdata_i[31]}}, data_rdata_i[31:16]};
			2'b11:
				if (!data_sign_ext_q)
					rdata_h_ext = {16'h0000, data_rdata_i[7:0], rdata_q[31:24]};
				else
					rdata_h_ext = {{16 {data_rdata_i[7]}}, data_rdata_i[7:0], rdata_q[31:24]};
			default: rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
		endcase
	always @(*)
		case (rdata_offset_q)
			2'b00:
				if (!data_sign_ext_q)
					rdata_b_ext = {24'h000000, data_rdata_i[7:0]};
				else
					rdata_b_ext = {{24 {data_rdata_i[7]}}, data_rdata_i[7:0]};
			2'b01:
				if (!data_sign_ext_q)
					rdata_b_ext = {24'h000000, data_rdata_i[15:8]};
				else
					rdata_b_ext = {{24 {data_rdata_i[15]}}, data_rdata_i[15:8]};
			2'b10:
				if (!data_sign_ext_q)
					rdata_b_ext = {24'h000000, data_rdata_i[23:16]};
				else
					rdata_b_ext = {{24 {data_rdata_i[23]}}, data_rdata_i[23:16]};
			2'b11:
				if (!data_sign_ext_q)
					rdata_b_ext = {24'h000000, data_rdata_i[31:24]};
				else
					rdata_b_ext = {{24 {data_rdata_i[31]}}, data_rdata_i[31:24]};
			default: rdata_b_ext = {24'h000000, data_rdata_i[7:0]};
		endcase
	always @(*)
		case (data_type_q)
			2'b00: data_rdata_ext = rdata_w_ext;
			2'b01: data_rdata_ext = rdata_h_ext;
			2'b10, 2'b11: data_rdata_ext = rdata_b_ext;
			default: data_rdata_ext = rdata_w_ext;
		endcase
	generate
		if (MemECC) begin : g_mem_rdata_ecc
			wire [1:0] ecc_err;
			wire [MemDataWidth - 1:0] data_rdata_buf;
			prim_buf #(.Width(MemDataWidth)) u_prim_buf_instr_rdata(
				.in_i(data_rdata_i),
				.out_o(data_rdata_buf)
			);
			prim_secded_inv_39_32_dec u_data_intg_dec(
				.data_i(data_rdata_buf),
				.data_o(),
				.syndrome_o(),
				.err_o(ecc_err)
			);
			assign data_intg_err = |ecc_err;
		end
		else begin : g_no_mem_data_ecc
			assign data_intg_err = 1'b0;
		end
	endgenerate
	assign split_misaligned_access = ((lsu_type_i == 2'b00) && (data_offset != 2'b00)) || ((lsu_type_i == 2'b01) && (data_offset == 2'b11));
	always @(*) begin
		ls_fsm_ns = ls_fsm_cs;
		data_req_o = 1'b0;
		addr_incr_req_o = 1'b0;
		handle_misaligned_d = handle_misaligned_q;
		pmp_err_d = pmp_err_q;
		lsu_err_d = lsu_err_q;
		addr_update = 1'b0;
		ctrl_update = 1'b0;
		rdata_update = 1'b0;
		perf_load_o = 1'b0;
		perf_store_o = 1'b0;
		case (ls_fsm_cs)
			3'd0: begin
				pmp_err_d = 1'b0;
				if (lsu_req_i) begin
					data_req_o = 1'b1;
					pmp_err_d = data_pmp_err_i;
					lsu_err_d = 1'b0;
					perf_load_o = ~lsu_we_i;
					perf_store_o = lsu_we_i;
					if (data_gnt_i) begin
						ctrl_update = 1'b1;
						addr_update = 1'b1;
						handle_misaligned_d = split_misaligned_access;
						ls_fsm_ns = (split_misaligned_access ? 3'd2 : 3'd0);
					end
					else
						ls_fsm_ns = (split_misaligned_access ? 3'd1 : 3'd3);
				end
			end
			3'd1: begin
				data_req_o = 1'b1;
				if (data_gnt_i || pmp_err_q) begin
					addr_update = 1'b1;
					ctrl_update = 1'b1;
					handle_misaligned_d = 1'b1;
					ls_fsm_ns = 3'd2;
				end
			end
			3'd2: begin
				data_req_o = 1'b1;
				addr_incr_req_o = 1'b1;
				if (data_rvalid_i || pmp_err_q) begin
					pmp_err_d = data_pmp_err_i;
					lsu_err_d = data_bus_err_i | pmp_err_q;
					rdata_update = ~data_we_q;
					ls_fsm_ns = (data_gnt_i ? 3'd0 : 3'd3);
					addr_update = data_gnt_i & ~(data_bus_err_i | pmp_err_q);
					handle_misaligned_d = ~data_gnt_i;
				end
				else if (data_gnt_i) begin
					ls_fsm_ns = 3'd4;
					handle_misaligned_d = 1'b0;
				end
			end
			3'd3: begin
				addr_incr_req_o = handle_misaligned_q;
				data_req_o = 1'b1;
				if (data_gnt_i || pmp_err_q) begin
					ctrl_update = 1'b1;
					addr_update = ~lsu_err_q;
					ls_fsm_ns = 3'd0;
					handle_misaligned_d = 1'b0;
				end
			end
			3'd4: begin
				addr_incr_req_o = 1'b1;
				if (data_rvalid_i) begin
					pmp_err_d = data_pmp_err_i;
					lsu_err_d = data_bus_err_i;
					addr_update = ~data_bus_err_i;
					rdata_update = ~data_we_q;
					ls_fsm_ns = 3'd0;
				end
			end
			default: ls_fsm_ns = 3'd0;
		endcase
	end
	assign lsu_req_done_o = (lsu_req_i | (ls_fsm_cs != 3'd0)) & (ls_fsm_ns == 3'd0);
	always @(posedge clk_i)
		if (!rst_ni) begin
			ls_fsm_cs <= 3'd0;
			handle_misaligned_q <= 1'sb0;
			pmp_err_q <= 1'sb0;
			lsu_err_q <= 1'sb0;
		end
		else begin
			ls_fsm_cs <= ls_fsm_ns;
			handle_misaligned_q <= handle_misaligned_d;
			pmp_err_q <= pmp_err_d;
			lsu_err_q <= lsu_err_d;
		end
	assign data_or_pmp_err = (lsu_err_q | data_bus_err_i) | pmp_err_q;
	assign lsu_resp_valid_o = (data_rvalid_i | pmp_err_q) & (ls_fsm_cs == 3'd0);
	assign lsu_rdata_valid_o = ((((ls_fsm_cs == 3'd0) & data_rvalid_i) & ~data_or_pmp_err) & ~data_we_q) & ~data_intg_err;
	assign lsu_rdata_o = data_rdata_ext;
	assign data_addr_w_aligned = {data_addr[31:2], 2'b00};
	assign data_addr_o = data_addr_w_aligned;
	assign data_we_o = lsu_we_i;
	assign data_be_o = data_be;
	generate
		if (MemECC) begin : g_mem_wdata_ecc
			prim_secded_inv_39_32_enc u_data_gen(
				.data_i(data_wdata),
				.data_o(data_wdata_o)
			);
		end
		else begin : g_no_mem_wdata_ecc
			assign data_wdata_o = data_wdata;
		end
	endgenerate
	assign addr_last_o = addr_last_q;
	assign load_err_o = (data_or_pmp_err & ~data_we_q) & lsu_resp_valid_o;
	assign store_err_o = (data_or_pmp_err & data_we_q) & lsu_resp_valid_o;
	assign load_resp_intg_err_o = (data_intg_err & data_rvalid_i) & ~data_we_q;
	assign store_resp_intg_err_o = (data_intg_err & data_rvalid_i) & data_we_q;
	assign busy_o = ls_fsm_cs != 3'd0;
endmodule
module ibex_wb_stage (
	clk_i,
	rst_ni,
	en_wb_i,
	instr_type_wb_i,
	pc_id_i,
	instr_is_compressed_id_i,
	instr_perf_count_id_i,
	ready_wb_o,
	rf_write_wb_o,
	outstanding_load_wb_o,
	outstanding_store_wb_o,
	pc_wb_o,
	perf_instr_ret_wb_o,
	perf_instr_ret_compressed_wb_o,
	perf_instr_ret_wb_spec_o,
	perf_instr_ret_compressed_wb_spec_o,
	rf_waddr_id_i,
	rf_wdata_id_i,
	rf_we_id_i,
	dummy_instr_id_i,
	rf_wdata_lsu_i,
	rf_we_lsu_i,
	rf_wdata_fwd_wb_o,
	rf_waddr_wb_o,
	rf_wdata_wb_o,
	rf_we_wb_o,
	dummy_instr_wb_o,
	lsu_resp_valid_i,
	lsu_resp_err_i,
	instr_done_wb_o
);
	parameter [0:0] ResetAll = 1'b0;
	parameter [0:0] WritebackStage = 1'b0;
	parameter [0:0] DummyInstructions = 1'b0;
	input wire clk_i;
	input wire rst_ni;
	input wire en_wb_i;
	input wire [1:0] instr_type_wb_i;
	input wire [31:0] pc_id_i;
	input wire instr_is_compressed_id_i;
	input wire instr_perf_count_id_i;
	output wire ready_wb_o;
	output wire rf_write_wb_o;
	output wire outstanding_load_wb_o;
	output wire outstanding_store_wb_o;
	output wire [31:0] pc_wb_o;
	output wire perf_instr_ret_wb_o;
	output wire perf_instr_ret_compressed_wb_o;
	output wire perf_instr_ret_wb_spec_o;
	output wire perf_instr_ret_compressed_wb_spec_o;
	input wire [4:0] rf_waddr_id_i;
	input wire [31:0] rf_wdata_id_i;
	input wire rf_we_id_i;
	input wire dummy_instr_id_i;
	input wire [31:0] rf_wdata_lsu_i;
	input wire rf_we_lsu_i;
	output wire [31:0] rf_wdata_fwd_wb_o;
	output wire [4:0] rf_waddr_wb_o;
	output wire [31:0] rf_wdata_wb_o;
	output wire rf_we_wb_o;
	output wire dummy_instr_wb_o;
	input wire lsu_resp_valid_i;
	input wire lsu_resp_err_i;
	output wire instr_done_wb_o;
	wire [31:0] rf_wdata_wb_mux [0:1];
	wire [1:0] rf_wdata_wb_mux_we;
	generate
		if (WritebackStage) begin : g_writeback_stage
			reg [31:0] rf_wdata_wb_q;
			reg rf_we_wb_q;
			reg [4:0] rf_waddr_wb_q;
			wire wb_done;
			reg wb_valid_q;
			reg [31:0] wb_pc_q;
			reg wb_compressed_q;
			reg wb_count_q;
			reg [1:0] wb_instr_type_q;
			wire wb_valid_d;
			assign wb_valid_d = (en_wb_i & ready_wb_o) | (wb_valid_q & ~wb_done);
			assign wb_done = (wb_instr_type_q == 2'd2) | lsu_resp_valid_i;
			always @(posedge clk_i)
				if (!rst_ni)
					wb_valid_q <= 1'b0;
				else
					wb_valid_q <= wb_valid_d;
			if (ResetAll) begin : g_wb_regs_ra
				always @(posedge clk_i)
					if (!rst_ni) begin
						rf_we_wb_q <= 1'sb0;
						rf_waddr_wb_q <= 1'sb0;
						rf_wdata_wb_q <= 1'sb0;
						wb_instr_type_q <= 2'd0;
						wb_pc_q <= 1'sb0;
						wb_compressed_q <= 1'sb0;
						wb_count_q <= 1'sb0;
					end
					else if (en_wb_i) begin
						rf_we_wb_q <= rf_we_id_i;
						rf_waddr_wb_q <= rf_waddr_id_i;
						rf_wdata_wb_q <= rf_wdata_id_i;
						wb_instr_type_q <= instr_type_wb_i;
						wb_pc_q <= pc_id_i;
						wb_compressed_q <= instr_is_compressed_id_i;
						wb_count_q <= instr_perf_count_id_i;
					end
			end
			else begin : g_wb_regs_nr
				always @(posedge clk_i)
					if (en_wb_i) begin
						rf_we_wb_q <= rf_we_id_i;
						rf_waddr_wb_q <= rf_waddr_id_i;
						rf_wdata_wb_q <= rf_wdata_id_i;
						wb_instr_type_q <= instr_type_wb_i;
						wb_pc_q <= pc_id_i;
						wb_compressed_q <= instr_is_compressed_id_i;
						wb_count_q <= instr_perf_count_id_i;
					end
			end
			assign rf_waddr_wb_o = rf_waddr_wb_q;
			assign rf_wdata_wb_mux[0] = rf_wdata_wb_q;
			assign rf_wdata_wb_mux_we[0] = rf_we_wb_q & wb_valid_q;
			assign ready_wb_o = ~wb_valid_q | wb_done;
			assign rf_write_wb_o = wb_valid_q & (rf_we_wb_q | (wb_instr_type_q == 2'd0));
			assign outstanding_load_wb_o = wb_valid_q & (wb_instr_type_q == 2'd0);
			assign outstanding_store_wb_o = wb_valid_q & (wb_instr_type_q == 2'd1);
			assign pc_wb_o = wb_pc_q;
			assign instr_done_wb_o = wb_valid_q & wb_done;
			assign perf_instr_ret_wb_spec_o = wb_count_q;
			assign perf_instr_ret_compressed_wb_spec_o = perf_instr_ret_wb_spec_o & wb_compressed_q;
			assign perf_instr_ret_wb_o = (instr_done_wb_o & wb_count_q) & ~(lsu_resp_valid_i & lsu_resp_err_i);
			assign perf_instr_ret_compressed_wb_o = perf_instr_ret_wb_o & wb_compressed_q;
			assign rf_wdata_fwd_wb_o = rf_wdata_wb_q;
			assign rf_wdata_wb_mux_we[1] = outstanding_load_wb_o & rf_we_lsu_i;
			if (DummyInstructions) begin : g_dummy_instr_wb
				reg dummy_instr_wb_q;
				if (ResetAll) begin : g_dummy_instr_wb_regs_ra
					always @(posedge clk_i)
						if (!rst_ni)
							dummy_instr_wb_q <= 1'b0;
						else if (en_wb_i)
							dummy_instr_wb_q <= dummy_instr_id_i;
				end
				else begin : g_dummy_instr_wb_regs_nr
					always @(posedge clk_i)
						if (en_wb_i)
							dummy_instr_wb_q <= dummy_instr_id_i;
				end
				assign dummy_instr_wb_o = dummy_instr_wb_q;
			end
			else begin : g_no_dummy_instr_wb
				wire unused_dummy_instr_id;
				assign unused_dummy_instr_id = dummy_instr_id_i;
				assign dummy_instr_wb_o = 1'b0;
			end
		end
		else begin : g_bypass_wb
			assign rf_waddr_wb_o = rf_waddr_id_i;
			assign rf_wdata_wb_mux[0] = rf_wdata_id_i;
			assign rf_wdata_wb_mux_we[0] = rf_we_id_i;
			assign rf_wdata_wb_mux_we[1] = rf_we_lsu_i;
			assign dummy_instr_wb_o = dummy_instr_id_i;
			assign perf_instr_ret_wb_spec_o = 1'b0;
			assign perf_instr_ret_compressed_wb_spec_o = 1'b0;
			assign perf_instr_ret_wb_o = (instr_perf_count_id_i & en_wb_i) & ~(lsu_resp_valid_i & lsu_resp_err_i);
			assign perf_instr_ret_compressed_wb_o = perf_instr_ret_wb_o & instr_is_compressed_id_i;
			assign ready_wb_o = 1'b1;
			wire unused_clk;
			wire unused_rst;
			wire [1:0] unused_instr_type_wb;
			wire [31:0] unused_pc_id;
			wire unused_dummy_instr_id;
			assign unused_clk = clk_i;
			assign unused_rst = rst_ni;
			assign unused_instr_type_wb = instr_type_wb_i;
			assign unused_pc_id = pc_id_i;
			assign unused_dummy_instr_id = dummy_instr_id_i;
			assign outstanding_load_wb_o = 1'b0;
			assign outstanding_store_wb_o = 1'b0;
			assign pc_wb_o = 1'sb0;
			assign rf_write_wb_o = 1'b0;
			assign rf_wdata_fwd_wb_o = 32'b00000000000000000000000000000000;
			assign instr_done_wb_o = 1'b0;
		end
	endgenerate
	assign rf_wdata_wb_mux[1] = rf_wdata_lsu_i;
	assign rf_wdata_wb_o = ({32 {rf_wdata_wb_mux_we[0]}} & rf_wdata_wb_mux[0]) | ({32 {rf_wdata_wb_mux_we[1]}} & rf_wdata_wb_mux[1]);
	assign rf_we_wb_o = |rf_wdata_wb_mux_we;
endmodule
module ibex_core (
	clk_i,
	rst_ni,
	hart_id_i,
	boot_addr_i,
	instr_req_o,
	instr_gnt_i,
	instr_rvalid_i,
	instr_addr_o,
	instr_rdata_i,
	instr_err_i,
	data_req_o,
	data_gnt_i,
	data_rvalid_i,
	data_we_o,
	data_be_o,
	data_addr_o,
	data_wdata_o,
	data_rdata_i,
	data_err_i,
	dummy_instr_id_o,
	dummy_instr_wb_o,
	rf_raddr_a_o,
	rf_raddr_b_o,
	rf_waddr_wb_o,
	rf_we_wb_o,
	rf_wdata_wb_ecc_o,
	rf_rdata_a_ecc_i,
	rf_rdata_b_ecc_i,
	ic_tag_req_o,
	ic_tag_write_o,
	ic_tag_addr_o,
	ic_tag_wdata_o,
	ic_tag_rdata_i,
	ic_data_req_o,
	ic_data_write_o,
	ic_data_addr_o,
	ic_data_wdata_o,
	ic_data_rdata_i,
	ic_scr_key_valid_i,
	ic_scr_key_req_o,
	irq_software_i,
	irq_timer_i,
	irq_external_i,
	irq_fast_i,
	irq_nm_i,
	irq_pending_o,
	debug_req_i,
	crash_dump_o,
	double_fault_seen_o,
	fetch_enable_i,
	alert_minor_o,
	alert_major_internal_o,
	alert_major_bus_o,
	core_busy_o
);
	parameter [0:0] PMPEnable = 1'b0;
	parameter [31:0] PMPGranularity = 0;
	parameter [31:0] PMPNumRegions = 4;
	parameter [31:0] MHPMCounterNum = 0;
	parameter [31:0] MHPMCounterWidth = 40;
	parameter [0:0] RV32E = 1'b0;
	parameter integer RV32M = 32'sd2;
	parameter integer RV32B = 32'sd0;
	parameter [0:0] BranchTargetALU = 1'b0;
	parameter [0:0] WritebackStage = 1'b0;
	parameter [0:0] ICache = 1'b0;
	parameter [0:0] ICacheECC = 1'b0;
	localparam [31:0] ibex_pkg_BUS_SIZE = 32;
	parameter [31:0] BusSizeECC = ibex_pkg_BUS_SIZE;
	localparam [31:0] ibex_pkg_ADDR_W = 32;
	localparam [31:0] ibex_pkg_IC_LINE_SIZE = 64;
	localparam [31:0] ibex_pkg_IC_LINE_BYTES = 8;
	localparam [31:0] ibex_pkg_IC_NUM_WAYS = 2;
	localparam [31:0] ibex_pkg_IC_SIZE_BYTES = 4096;
	localparam [31:0] ibex_pkg_IC_NUM_LINES = (ibex_pkg_IC_SIZE_BYTES / ibex_pkg_IC_NUM_WAYS) / ibex_pkg_IC_LINE_BYTES;
	localparam [31:0] ibex_pkg_IC_INDEX_W = $clog2(ibex_pkg_IC_NUM_LINES);
	localparam [31:0] ibex_pkg_IC_LINE_W = 3;
	localparam [31:0] ibex_pkg_IC_TAG_SIZE = ((ibex_pkg_ADDR_W - ibex_pkg_IC_INDEX_W) - ibex_pkg_IC_LINE_W) + 1;
	parameter [31:0] TagSizeECC = ibex_pkg_IC_TAG_SIZE;
	parameter [31:0] LineSizeECC = ibex_pkg_IC_LINE_SIZE;
	parameter [0:0] BranchPredictor = 1'b0;
	parameter [0:0] DbgTriggerEn = 1'b0;
	parameter [31:0] DbgHwBreakNum = 1;
	parameter [0:0] ResetAll = 1'b0;
	localparam signed [31:0] ibex_pkg_LfsrWidth = 32;
	localparam [31:0] ibex_pkg_RndCnstLfsrSeedDefault = 32'hac533bf4;
	parameter [31:0] RndCnstLfsrSeed = ibex_pkg_RndCnstLfsrSeedDefault;
	localparam [159:0] ibex_pkg_RndCnstLfsrPermDefault = 160'h1e35ecba467fd1b12e958152c04fa43878a8daed;
	parameter [159:0] RndCnstLfsrPerm = ibex_pkg_RndCnstLfsrPermDefault;
	parameter [0:0] SecureIbex = 1'b0;
	parameter [0:0] DummyInstructions = 1'b0;
	parameter [0:0] RegFileECC = 1'b0;
	parameter [31:0] RegFileDataWidth = 32;
	parameter [0:0] MemECC = 1'b0;
	parameter [31:0] MemDataWidth = (MemECC ? 39 : 32);
	parameter [31:0] DmHaltAddr = 32'h1a110800;
	parameter [31:0] DmExceptionAddr = 32'h1a110808;
	input wire clk_i;
	input wire rst_ni;
	input wire [31:0] hart_id_i;
	input wire [31:0] boot_addr_i;
	output wire instr_req_o;
	input wire instr_gnt_i;
	input wire instr_rvalid_i;
	output wire [31:0] instr_addr_o;
	input wire [MemDataWidth - 1:0] instr_rdata_i;
	input wire instr_err_i;
	output wire data_req_o;
	input wire data_gnt_i;
	input wire data_rvalid_i;
	output wire data_we_o;
	output wire [3:0] data_be_o;
	output wire [31:0] data_addr_o;
	output wire [MemDataWidth - 1:0] data_wdata_o;
	input wire [MemDataWidth - 1:0] data_rdata_i;
	input wire data_err_i;
	output wire dummy_instr_id_o;
	output wire dummy_instr_wb_o;
	output wire [4:0] rf_raddr_a_o;
	output wire [4:0] rf_raddr_b_o;
	output wire [4:0] rf_waddr_wb_o;
	output wire rf_we_wb_o;
	output wire [RegFileDataWidth - 1:0] rf_wdata_wb_ecc_o;
	input wire [RegFileDataWidth - 1:0] rf_rdata_a_ecc_i;
	input wire [RegFileDataWidth - 1:0] rf_rdata_b_ecc_i;
	output wire [1:0] ic_tag_req_o;
	output wire ic_tag_write_o;
	output wire [ibex_pkg_IC_INDEX_W - 1:0] ic_tag_addr_o;
	output wire [TagSizeECC - 1:0] ic_tag_wdata_o;
	input wire [(ibex_pkg_IC_NUM_WAYS * TagSizeECC) - 1:0] ic_tag_rdata_i;
	output wire [1:0] ic_data_req_o;
	output wire ic_data_write_o;
	output wire [ibex_pkg_IC_INDEX_W - 1:0] ic_data_addr_o;
	output wire [LineSizeECC - 1:0] ic_data_wdata_o;
	input wire [(ibex_pkg_IC_NUM_WAYS * LineSizeECC) - 1:0] ic_data_rdata_i;
	input wire ic_scr_key_valid_i;
	output wire ic_scr_key_req_o;
	input wire irq_software_i;
	input wire irq_timer_i;
	input wire irq_external_i;
	input wire [14:0] irq_fast_i;
	input wire irq_nm_i;
	output wire irq_pending_o;
	input wire debug_req_i;
	output wire [159:0] crash_dump_o;
	output wire double_fault_seen_o;
	input wire [3:0] fetch_enable_i;
	output wire alert_minor_o;
	output wire alert_major_internal_o;
	output wire alert_major_bus_o;
	output wire [3:0] core_busy_o;
	localparam [31:0] PMPNumChan = 3;
	localparam [0:0] DataIndTiming = SecureIbex;
	localparam [0:0] PCIncrCheck = SecureIbex;
	localparam [0:0] ShadowCSR = 1'b0;
	wire dummy_instr_id;
	wire instr_valid_id;
	wire instr_new_id;
	wire [31:0] instr_rdata_id;
	wire [31:0] instr_rdata_alu_id;
	wire [15:0] instr_rdata_c_id;
	wire instr_is_compressed_id;
	wire instr_perf_count_id;
	wire instr_bp_taken_id;
	wire instr_fetch_err;
	wire instr_fetch_err_plus2;
	wire illegal_c_insn_id;
	wire [31:0] pc_if;
	wire [31:0] pc_id;
	wire [31:0] pc_wb;
	wire [67:0] imd_val_d_ex;
	wire [67:0] imd_val_q_ex;
	wire [1:0] imd_val_we_ex;
	wire data_ind_timing;
	wire dummy_instr_en;
	wire [2:0] dummy_instr_mask;
	wire dummy_instr_seed_en;
	wire [31:0] dummy_instr_seed;
	wire icache_enable;
	wire icache_inval;
	wire icache_ecc_error;
	wire pc_mismatch_alert;
	wire csr_shadow_err;
	wire instr_first_cycle_id;
	wire instr_valid_clear;
	wire pc_set;
	wire nt_branch_mispredict;
	wire [31:0] nt_branch_addr;
	wire [2:0] pc_mux_id;
	wire [1:0] exc_pc_mux_id;
	wire [6:0] exc_cause;
	wire instr_intg_err;
	wire lsu_load_err;
	wire lsu_store_err;
	wire lsu_load_resp_intg_err;
	wire lsu_store_resp_intg_err;
	wire lsu_addr_incr_req;
	wire [31:0] lsu_addr_last;
	wire [31:0] branch_target_ex;
	wire branch_decision;
	wire ctrl_busy;
	wire if_busy;
	wire lsu_busy;
	wire [4:0] rf_raddr_a;
	wire [31:0] rf_rdata_a;
	wire [4:0] rf_raddr_b;
	wire [31:0] rf_rdata_b;
	wire rf_ren_a;
	wire rf_ren_b;
	wire [4:0] rf_waddr_wb;
	wire [31:0] rf_wdata_wb;
	wire [31:0] rf_wdata_fwd_wb;
	wire [31:0] rf_wdata_lsu;
	wire rf_we_wb;
	wire rf_we_lsu;
	wire rf_ecc_err_comb;
	wire [4:0] rf_waddr_id;
	wire [31:0] rf_wdata_id;
	wire rf_we_id;
	wire rf_rd_a_wb_match;
	wire rf_rd_b_wb_match;
	wire [6:0] alu_operator_ex;
	wire [31:0] alu_operand_a_ex;
	wire [31:0] alu_operand_b_ex;
	wire [31:0] bt_a_operand;
	wire [31:0] bt_b_operand;
	wire [31:0] alu_adder_result_ex;
	wire [31:0] result_ex;
	wire mult_en_ex;
	wire div_en_ex;
	wire mult_sel_ex;
	wire div_sel_ex;
	wire [1:0] multdiv_operator_ex;
	wire [1:0] multdiv_signed_mode_ex;
	wire [31:0] multdiv_operand_a_ex;
	wire [31:0] multdiv_operand_b_ex;
	wire multdiv_ready_id;
	wire csr_access;
	wire [1:0] csr_op;
	wire csr_op_en;
	wire [11:0] csr_addr;
	wire [31:0] csr_rdata;
	wire [31:0] csr_wdata;
	wire illegal_csr_insn_id;
	wire lsu_we;
	wire [1:0] lsu_type;
	wire lsu_sign_ext;
	wire lsu_req;
	wire [31:0] lsu_wdata;
	wire lsu_req_done;
	wire id_in_ready;
	wire ex_valid;
	wire lsu_resp_valid;
	wire lsu_resp_err;
	wire instr_req_int;
	wire instr_req_gated;
	wire instr_exec;
	wire en_wb;
	wire [1:0] instr_type_wb;
	wire ready_wb;
	wire rf_write_wb;
	wire outstanding_load_wb;
	wire outstanding_store_wb;
	wire dummy_instr_wb;
	wire nmi_mode;
	wire [17:0] irqs;
	wire csr_mstatus_mie;
	wire [31:0] csr_mepc;
	wire [31:0] csr_depc;
	wire [(PMPNumRegions * 34) - 1:0] csr_pmp_addr;
	wire [(PMPNumRegions * 6) - 1:0] csr_pmp_cfg;
	wire [2:0] csr_pmp_mseccfg;
	wire [0:2] pmp_req_err;
	wire data_req_out;
	wire csr_save_if;
	wire csr_save_id;
	wire csr_save_wb;
	wire csr_restore_mret_id;
	wire csr_restore_dret_id;
	wire csr_save_cause;
	wire csr_mtvec_init;
	wire [31:0] csr_mtvec;
	wire [31:0] csr_mtval;
	wire csr_mstatus_tw;
	wire [1:0] priv_mode_id;
	wire [1:0] priv_mode_lsu;
	wire debug_mode;
	wire debug_mode_entering;
	wire [2:0] debug_cause;
	wire debug_csr_save;
	wire debug_single_step;
	wire debug_ebreakm;
	wire debug_ebreaku;
	wire trigger_match;
	wire instr_id_done;
	wire instr_done_wb;
	wire perf_instr_ret_wb;
	wire perf_instr_ret_compressed_wb;
	wire perf_instr_ret_wb_spec;
	wire perf_instr_ret_compressed_wb_spec;
	wire perf_iside_wait;
	wire perf_dside_wait;
	wire perf_mul_wait;
	wire perf_div_wait;
	wire perf_jump;
	wire perf_branch;
	wire perf_tbranch;
	wire perf_load;
	wire perf_store;
	wire illegal_insn_id;
	wire unused_illegal_insn_id;
	localparam [3:0] ibex_pkg_IbexMuBiOff = 4'b1010;
	localparam [3:0] ibex_pkg_IbexMuBiOn = 4'b0101;
	generate
		if (SecureIbex) begin : g_core_busy_secure
			localparam [31:0] NumBusySignals = 3;
			localparam [31:0] NumBusyBits = 12;
			wire [11:0] busy_bits_buf;
			prim_buf #(.Width(NumBusyBits)) u_fetch_enable_buf(
				.in_i({4 {ctrl_busy, if_busy, lsu_busy}}),
				.out_o(busy_bits_buf)
			);
			genvar i;
			for (i = 0; i < 4; i = i + 1) begin : g_core_busy_bits
				if (ibex_pkg_IbexMuBiOn[i] == 1'b1) begin : g_pos
					assign core_busy_o[i] = |busy_bits_buf[i * NumBusySignals+:NumBusySignals];
				end
				else begin : g_neg
					assign core_busy_o[i] = ~|busy_bits_buf[i * NumBusySignals+:NumBusySignals];
				end
			end
		end
		else begin : g_core_busy_non_secure
			assign core_busy_o = ((ctrl_busy || if_busy) || lsu_busy ? ibex_pkg_IbexMuBiOn : ibex_pkg_IbexMuBiOff);
		end
	endgenerate
	localparam [31:0] ibex_pkg_PMP_I = 0;
	localparam [31:0] ibex_pkg_PMP_I2 = 1;
	ibex_if_stage #(
		.DmHaltAddr(DmHaltAddr),
		.DmExceptionAddr(DmExceptionAddr),
		.DummyInstructions(DummyInstructions),
		.ICache(ICache),
		.ICacheECC(ICacheECC),
		.BusSizeECC(BusSizeECC),
		.TagSizeECC(TagSizeECC),
		.LineSizeECC(LineSizeECC),
		.PCIncrCheck(PCIncrCheck),
		.ResetAll(ResetAll),
		.RndCnstLfsrSeed(RndCnstLfsrSeed),
		.RndCnstLfsrPerm(RndCnstLfsrPerm),
		.BranchPredictor(BranchPredictor),
		.MemECC(MemECC),
		.MemDataWidth(MemDataWidth)
	) if_stage_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.boot_addr_i(boot_addr_i),
		.req_i(instr_req_gated),
		.instr_req_o(instr_req_o),
		.instr_addr_o(instr_addr_o),
		.instr_gnt_i(instr_gnt_i),
		.instr_rvalid_i(instr_rvalid_i),
		.instr_rdata_i(instr_rdata_i),
		.instr_bus_err_i(instr_err_i),
		.instr_intg_err_o(instr_intg_err),
		.ic_tag_req_o(ic_tag_req_o),
		.ic_tag_write_o(ic_tag_write_o),
		.ic_tag_addr_o(ic_tag_addr_o),
		.ic_tag_wdata_o(ic_tag_wdata_o),
		.ic_tag_rdata_i(ic_tag_rdata_i),
		.ic_data_req_o(ic_data_req_o),
		.ic_data_write_o(ic_data_write_o),
		.ic_data_addr_o(ic_data_addr_o),
		.ic_data_wdata_o(ic_data_wdata_o),
		.ic_data_rdata_i(ic_data_rdata_i),
		.ic_scr_key_valid_i(ic_scr_key_valid_i),
		.ic_scr_key_req_o(ic_scr_key_req_o),
		.instr_valid_id_o(instr_valid_id),
		.instr_new_id_o(instr_new_id),
		.instr_rdata_id_o(instr_rdata_id),
		.instr_rdata_alu_id_o(instr_rdata_alu_id),
		.instr_rdata_c_id_o(instr_rdata_c_id),
		.instr_is_compressed_id_o(instr_is_compressed_id),
		.instr_bp_taken_o(instr_bp_taken_id),
		.instr_fetch_err_o(instr_fetch_err),
		.instr_fetch_err_plus2_o(instr_fetch_err_plus2),
		.illegal_c_insn_id_o(illegal_c_insn_id),
		.dummy_instr_id_o(dummy_instr_id),
		.pc_if_o(pc_if),
		.pc_id_o(pc_id),
		.pmp_err_if_i(pmp_req_err[ibex_pkg_PMP_I]),
		.pmp_err_if_plus2_i(pmp_req_err[ibex_pkg_PMP_I2]),
		.instr_valid_clear_i(instr_valid_clear),
		.pc_set_i(pc_set),
		.pc_mux_i(pc_mux_id),
		.nt_branch_mispredict_i(nt_branch_mispredict),
		.exc_pc_mux_i(exc_pc_mux_id),
		.exc_cause(exc_cause),
		.dummy_instr_en_i(dummy_instr_en),
		.dummy_instr_mask_i(dummy_instr_mask),
		.dummy_instr_seed_en_i(dummy_instr_seed_en),
		.dummy_instr_seed_i(dummy_instr_seed),
		.icache_enable_i(icache_enable),
		.icache_inval_i(icache_inval),
		.icache_ecc_error_o(icache_ecc_error),
		.branch_target_ex_i(branch_target_ex),
		.nt_branch_addr_i(nt_branch_addr),
		.csr_mepc_i(csr_mepc),
		.csr_depc_i(csr_depc),
		.csr_mtvec_i(csr_mtvec),
		.csr_mtvec_init_o(csr_mtvec_init),
		.id_in_ready_i(id_in_ready),
		.pc_mismatch_alert_o(pc_mismatch_alert),
		.if_busy_o(if_busy)
	);
	assign perf_iside_wait = id_in_ready & ~instr_valid_id;
	generate
		if (SecureIbex) begin : g_instr_req_gated_secure
			assign instr_req_gated = instr_req_int & (fetch_enable_i == ibex_pkg_IbexMuBiOn);
			assign instr_exec = fetch_enable_i == ibex_pkg_IbexMuBiOn;
		end
		else begin : g_instr_req_gated_non_secure
			wire unused_fetch_enable;
			assign unused_fetch_enable = ^fetch_enable_i[3:1];
			assign instr_req_gated = instr_req_int & fetch_enable_i[0];
			assign instr_exec = fetch_enable_i[0];
		end
	endgenerate
	ibex_id_stage #(
		.RV32E(RV32E),
		.RV32M(RV32M),
		.RV32B(RV32B),
		.BranchTargetALU(BranchTargetALU),
		.DataIndTiming(DataIndTiming),
		.WritebackStage(WritebackStage),
		.BranchPredictor(BranchPredictor),
		.MemECC(MemECC)
	) id_stage_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.ctrl_busy_o(ctrl_busy),
		.illegal_insn_o(illegal_insn_id),
		.instr_valid_i(instr_valid_id),
		.instr_rdata_i(instr_rdata_id),
		.instr_rdata_alu_i(instr_rdata_alu_id),
		.instr_rdata_c_i(instr_rdata_c_id),
		.instr_is_compressed_i(instr_is_compressed_id),
		.instr_bp_taken_i(instr_bp_taken_id),
		.branch_decision_i(branch_decision),
		.instr_first_cycle_id_o(instr_first_cycle_id),
		.instr_valid_clear_o(instr_valid_clear),
		.id_in_ready_o(id_in_ready),
		.instr_exec_i(instr_exec),
		.instr_req_o(instr_req_int),
		.pc_set_o(pc_set),
		.pc_mux_o(pc_mux_id),
		.nt_branch_mispredict_o(nt_branch_mispredict),
		.nt_branch_addr_o(nt_branch_addr),
		.exc_pc_mux_o(exc_pc_mux_id),
		.exc_cause_o(exc_cause),
		.icache_inval_o(icache_inval),
		.instr_fetch_err_i(instr_fetch_err),
		.instr_fetch_err_plus2_i(instr_fetch_err_plus2),
		.illegal_c_insn_i(illegal_c_insn_id),
		.pc_id_i(pc_id),
		.ex_valid_i(ex_valid),
		.lsu_resp_valid_i(lsu_resp_valid),
		.alu_operator_ex_o(alu_operator_ex),
		.alu_operand_a_ex_o(alu_operand_a_ex),
		.alu_operand_b_ex_o(alu_operand_b_ex),
		.imd_val_q_ex_o(imd_val_q_ex),
		.imd_val_d_ex_i(imd_val_d_ex),
		.imd_val_we_ex_i(imd_val_we_ex),
		.bt_a_operand_o(bt_a_operand),
		.bt_b_operand_o(bt_b_operand),
		.mult_en_ex_o(mult_en_ex),
		.div_en_ex_o(div_en_ex),
		.mult_sel_ex_o(mult_sel_ex),
		.div_sel_ex_o(div_sel_ex),
		.multdiv_operator_ex_o(multdiv_operator_ex),
		.multdiv_signed_mode_ex_o(multdiv_signed_mode_ex),
		.multdiv_operand_a_ex_o(multdiv_operand_a_ex),
		.multdiv_operand_b_ex_o(multdiv_operand_b_ex),
		.multdiv_ready_id_o(multdiv_ready_id),
		.csr_access_o(csr_access),
		.csr_op_o(csr_op),
		.csr_op_en_o(csr_op_en),
		.csr_save_if_o(csr_save_if),
		.csr_save_id_o(csr_save_id),
		.csr_save_wb_o(csr_save_wb),
		.csr_restore_mret_id_o(csr_restore_mret_id),
		.csr_restore_dret_id_o(csr_restore_dret_id),
		.csr_save_cause_o(csr_save_cause),
		.csr_mtval_o(csr_mtval),
		.priv_mode_i(priv_mode_id),
		.csr_mstatus_tw_i(csr_mstatus_tw),
		.illegal_csr_insn_i(illegal_csr_insn_id),
		.data_ind_timing_i(data_ind_timing),
		.lsu_req_o(lsu_req),
		.lsu_we_o(lsu_we),
		.lsu_type_o(lsu_type),
		.lsu_sign_ext_o(lsu_sign_ext),
		.lsu_wdata_o(lsu_wdata),
		.lsu_req_done_i(lsu_req_done),
		.lsu_addr_incr_req_i(lsu_addr_incr_req),
		.lsu_addr_last_i(lsu_addr_last),
		.lsu_load_err_i(lsu_load_err),
		.lsu_load_resp_intg_err_i(lsu_load_resp_intg_err),
		.lsu_store_err_i(lsu_store_err),
		.lsu_store_resp_intg_err_i(lsu_store_resp_intg_err),
		.csr_mstatus_mie_i(csr_mstatus_mie),
		.irq_pending_i(irq_pending_o),
		.irqs_i(irqs),
		.irq_nm_i(irq_nm_i),
		.nmi_mode_o(nmi_mode),
		.debug_mode_o(debug_mode),
		.debug_mode_entering_o(debug_mode_entering),
		.debug_cause_o(debug_cause),
		.debug_csr_save_o(debug_csr_save),
		.debug_req_i(debug_req_i),
		.debug_single_step_i(debug_single_step),
		.debug_ebreakm_i(debug_ebreakm),
		.debug_ebreaku_i(debug_ebreaku),
		.trigger_match_i(trigger_match),
		.result_ex_i(result_ex),
		.csr_rdata_i(csr_rdata),
		.rf_raddr_a_o(rf_raddr_a),
		.rf_rdata_a_i(rf_rdata_a),
		.rf_raddr_b_o(rf_raddr_b),
		.rf_rdata_b_i(rf_rdata_b),
		.rf_ren_a_o(rf_ren_a),
		.rf_ren_b_o(rf_ren_b),
		.rf_waddr_id_o(rf_waddr_id),
		.rf_wdata_id_o(rf_wdata_id),
		.rf_we_id_o(rf_we_id),
		.rf_rd_a_wb_match_o(rf_rd_a_wb_match),
		.rf_rd_b_wb_match_o(rf_rd_b_wb_match),
		.rf_waddr_wb_i(rf_waddr_wb),
		.rf_wdata_fwd_wb_i(rf_wdata_fwd_wb),
		.rf_write_wb_i(rf_write_wb),
		.en_wb_o(en_wb),
		.instr_type_wb_o(instr_type_wb),
		.instr_perf_count_id_o(instr_perf_count_id),
		.ready_wb_i(ready_wb),
		.outstanding_load_wb_i(outstanding_load_wb),
		.outstanding_store_wb_i(outstanding_store_wb),
		.perf_jump_o(perf_jump),
		.perf_branch_o(perf_branch),
		.perf_tbranch_o(perf_tbranch),
		.perf_dside_wait_o(perf_dside_wait),
		.perf_mul_wait_o(perf_mul_wait),
		.perf_div_wait_o(perf_div_wait),
		.instr_id_done_o(instr_id_done)
	);
	assign unused_illegal_insn_id = illegal_insn_id;
	ibex_ex_block #(
		.RV32M(RV32M),
		.RV32B(RV32B),
		.BranchTargetALU(BranchTargetALU)
	) ex_block_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.alu_operator_i(alu_operator_ex),
		.alu_operand_a_i(alu_operand_a_ex),
		.alu_operand_b_i(alu_operand_b_ex),
		.alu_instr_first_cycle_i(instr_first_cycle_id),
		.bt_a_operand_i(bt_a_operand),
		.bt_b_operand_i(bt_b_operand),
		.multdiv_operator_i(multdiv_operator_ex),
		.mult_en_i(mult_en_ex),
		.div_en_i(div_en_ex),
		.mult_sel_i(mult_sel_ex),
		.div_sel_i(div_sel_ex),
		.multdiv_signed_mode_i(multdiv_signed_mode_ex),
		.multdiv_operand_a_i(multdiv_operand_a_ex),
		.multdiv_operand_b_i(multdiv_operand_b_ex),
		.multdiv_ready_id_i(multdiv_ready_id),
		.data_ind_timing_i(data_ind_timing),
		.imd_val_we_o(imd_val_we_ex),
		.imd_val_d_o(imd_val_d_ex),
		.imd_val_q_i(imd_val_q_ex),
		.alu_adder_result_ex_o(alu_adder_result_ex),
		.result_ex_o(result_ex),
		.branch_target_o(branch_target_ex),
		.branch_decision_o(branch_decision),
		.ex_valid_o(ex_valid)
	);
	localparam [31:0] ibex_pkg_PMP_D = 2;
	assign data_req_o = data_req_out & ~pmp_req_err[ibex_pkg_PMP_D];
	assign lsu_resp_err = lsu_load_err | lsu_store_err;
	ibex_load_store_unit #(
		.MemECC(MemECC),
		.MemDataWidth(MemDataWidth)
	) load_store_unit_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.data_req_o(data_req_out),
		.data_gnt_i(data_gnt_i),
		.data_rvalid_i(data_rvalid_i),
		.data_bus_err_i(data_err_i),
		.data_pmp_err_i(pmp_req_err[ibex_pkg_PMP_D]),
		.data_addr_o(data_addr_o),
		.data_we_o(data_we_o),
		.data_be_o(data_be_o),
		.data_wdata_o(data_wdata_o),
		.data_rdata_i(data_rdata_i),
		.lsu_we_i(lsu_we),
		.lsu_type_i(lsu_type),
		.lsu_wdata_i(lsu_wdata),
		.lsu_sign_ext_i(lsu_sign_ext),
		.lsu_rdata_o(rf_wdata_lsu),
		.lsu_rdata_valid_o(rf_we_lsu),
		.lsu_req_i(lsu_req),
		.lsu_req_done_o(lsu_req_done),
		.adder_result_ex_i(alu_adder_result_ex),
		.addr_incr_req_o(lsu_addr_incr_req),
		.addr_last_o(lsu_addr_last),
		.lsu_resp_valid_o(lsu_resp_valid),
		.load_err_o(lsu_load_err),
		.load_resp_intg_err_o(lsu_load_resp_intg_err),
		.store_err_o(lsu_store_err),
		.store_resp_intg_err_o(lsu_store_resp_intg_err),
		.busy_o(lsu_busy),
		.perf_load_o(perf_load),
		.perf_store_o(perf_store)
	);
	ibex_wb_stage #(
		.ResetAll(ResetAll),
		.WritebackStage(WritebackStage),
		.DummyInstructions(DummyInstructions)
	) wb_stage_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.en_wb_i(en_wb),
		.instr_type_wb_i(instr_type_wb),
		.pc_id_i(pc_id),
		.instr_is_compressed_id_i(instr_is_compressed_id),
		.instr_perf_count_id_i(instr_perf_count_id),
		.ready_wb_o(ready_wb),
		.rf_write_wb_o(rf_write_wb),
		.outstanding_load_wb_o(outstanding_load_wb),
		.outstanding_store_wb_o(outstanding_store_wb),
		.pc_wb_o(pc_wb),
		.perf_instr_ret_wb_o(perf_instr_ret_wb),
		.perf_instr_ret_compressed_wb_o(perf_instr_ret_compressed_wb),
		.perf_instr_ret_wb_spec_o(perf_instr_ret_wb_spec),
		.perf_instr_ret_compressed_wb_spec_o(perf_instr_ret_compressed_wb_spec),
		.rf_waddr_id_i(rf_waddr_id),
		.rf_wdata_id_i(rf_wdata_id),
		.rf_we_id_i(rf_we_id),
		.dummy_instr_id_i(dummy_instr_id),
		.rf_wdata_lsu_i(rf_wdata_lsu),
		.rf_we_lsu_i(rf_we_lsu),
		.rf_wdata_fwd_wb_o(rf_wdata_fwd_wb),
		.rf_waddr_wb_o(rf_waddr_wb),
		.rf_wdata_wb_o(rf_wdata_wb),
		.rf_we_wb_o(rf_we_wb),
		.dummy_instr_wb_o(dummy_instr_wb),
		.lsu_resp_valid_i(lsu_resp_valid),
		.lsu_resp_err_i(lsu_resp_err),
		.instr_done_wb_o(instr_done_wb)
	);
	assign dummy_instr_id_o = dummy_instr_id;
	assign dummy_instr_wb_o = dummy_instr_wb;
	assign rf_raddr_a_o = rf_raddr_a;
	assign rf_waddr_wb_o = rf_waddr_wb;
	assign rf_we_wb_o = rf_we_wb;
	assign rf_raddr_b_o = rf_raddr_b;
	generate
		if (RegFileECC) begin : gen_regfile_ecc
			wire [1:0] rf_ecc_err_a;
			wire [1:0] rf_ecc_err_b;
			wire rf_ecc_err_a_id;
			wire rf_ecc_err_b_id;
			prim_secded_inv_39_32_enc regfile_ecc_enc(
				.data_i(rf_wdata_wb),
				.data_o(rf_wdata_wb_ecc_o)
			);
			prim_secded_inv_39_32_dec regfile_ecc_dec_a(
				.data_i(rf_rdata_a_ecc_i),
				.data_o(),
				.syndrome_o(),
				.err_o(rf_ecc_err_a)
			);
			prim_secded_inv_39_32_dec regfile_ecc_dec_b(
				.data_i(rf_rdata_b_ecc_i),
				.data_o(),
				.syndrome_o(),
				.err_o(rf_ecc_err_b)
			);
			assign rf_rdata_a = rf_rdata_a_ecc_i[31:0];
			assign rf_rdata_b = rf_rdata_b_ecc_i[31:0];
			assign rf_ecc_err_a_id = (|rf_ecc_err_a & rf_ren_a) & ~rf_rd_a_wb_match;
			assign rf_ecc_err_b_id = (|rf_ecc_err_b & rf_ren_b) & ~rf_rd_b_wb_match;
			assign rf_ecc_err_comb = instr_valid_id & (rf_ecc_err_a_id | rf_ecc_err_b_id);
		end
		else begin : gen_no_regfile_ecc
			wire unused_rf_ren_a;
			wire unused_rf_ren_b;
			wire unused_rf_rd_a_wb_match;
			wire unused_rf_rd_b_wb_match;
			assign unused_rf_ren_a = rf_ren_a;
			assign unused_rf_ren_b = rf_ren_b;
			assign unused_rf_rd_a_wb_match = rf_rd_a_wb_match;
			assign unused_rf_rd_b_wb_match = rf_rd_b_wb_match;
			assign rf_wdata_wb_ecc_o = rf_wdata_wb;
			assign rf_rdata_a = rf_rdata_a_ecc_i;
			assign rf_rdata_b = rf_rdata_b_ecc_i;
			assign rf_ecc_err_comb = 1'b0;
		end
	endgenerate
	wire [31:0] crash_dump_mtval;
	assign crash_dump_o[159-:32] = pc_id;
	assign crash_dump_o[127-:32] = pc_if;
	assign crash_dump_o[95-:32] = lsu_addr_last;
	assign crash_dump_o[63-:32] = csr_mepc;
	assign crash_dump_o[31-:32] = crash_dump_mtval;
	assign alert_minor_o = icache_ecc_error;
	assign alert_major_internal_o = (rf_ecc_err_comb | pc_mismatch_alert) | csr_shadow_err;
	assign alert_major_bus_o = (lsu_load_resp_intg_err | lsu_store_resp_intg_err) | instr_intg_err;
	assign csr_wdata = alu_operand_a_ex;
	function automatic [11:0] sv2v_cast_12;
		input reg [11:0] inp;
		sv2v_cast_12 = inp;
	endfunction
	assign csr_addr = sv2v_cast_12((csr_access ? alu_operand_b_ex[11:0] : 12'b000000000000));
	ibex_cs_registers #(
		.DbgTriggerEn(DbgTriggerEn),
		.DbgHwBreakNum(DbgHwBreakNum),
		.DataIndTiming(DataIndTiming),
		.DummyInstructions(DummyInstructions),
		.ShadowCSR(ShadowCSR),
		.ICache(ICache),
		.MHPMCounterNum(MHPMCounterNum),
		.MHPMCounterWidth(MHPMCounterWidth),
		.PMPEnable(PMPEnable),
		.PMPGranularity(PMPGranularity),
		.PMPNumRegions(PMPNumRegions),
		.RV32E(RV32E),
		.RV32M(RV32M),
		.RV32B(RV32B)
	) cs_registers_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.hart_id_i(hart_id_i),
		.priv_mode_id_o(priv_mode_id),
		.priv_mode_lsu_o(priv_mode_lsu),
		.csr_mtvec_o(csr_mtvec),
		.csr_mtvec_init_i(csr_mtvec_init),
		.boot_addr_i(boot_addr_i),
		.csr_access_i(csr_access),
		.csr_addr_i(csr_addr),
		.csr_wdata_i(csr_wdata),
		.csr_op_i(csr_op),
		.csr_op_en_i(csr_op_en),
		.csr_rdata_o(csr_rdata),
		.irq_software_i(irq_software_i),
		.irq_timer_i(irq_timer_i),
		.irq_external_i(irq_external_i),
		.irq_fast_i(irq_fast_i),
		.nmi_mode_i(nmi_mode),
		.irq_pending_o(irq_pending_o),
		.irqs_o(irqs),
		.csr_mstatus_mie_o(csr_mstatus_mie),
		.csr_mstatus_tw_o(csr_mstatus_tw),
		.csr_mepc_o(csr_mepc),
		.csr_mtval_o(crash_dump_mtval),
		.csr_pmp_cfg_o(csr_pmp_cfg),
		.csr_pmp_addr_o(csr_pmp_addr),
		.csr_pmp_mseccfg_o(csr_pmp_mseccfg),
		.csr_depc_o(csr_depc),
		.debug_mode_i(debug_mode),
		.debug_mode_entering_i(debug_mode_entering),
		.debug_cause_i(debug_cause),
		.debug_csr_save_i(debug_csr_save),
		.debug_single_step_o(debug_single_step),
		.debug_ebreakm_o(debug_ebreakm),
		.debug_ebreaku_o(debug_ebreaku),
		.trigger_match_o(trigger_match),
		.pc_if_i(pc_if),
		.pc_id_i(pc_id),
		.pc_wb_i(pc_wb),
		.data_ind_timing_o(data_ind_timing),
		.dummy_instr_en_o(dummy_instr_en),
		.dummy_instr_mask_o(dummy_instr_mask),
		.dummy_instr_seed_en_o(dummy_instr_seed_en),
		.dummy_instr_seed_o(dummy_instr_seed),
		.icache_enable_o(icache_enable),
		.csr_shadow_err_o(csr_shadow_err),
		.ic_scr_key_valid_i(ic_scr_key_valid_i),
		.csr_save_if_i(csr_save_if),
		.csr_save_id_i(csr_save_id),
		.csr_save_wb_i(csr_save_wb),
		.csr_restore_mret_i(csr_restore_mret_id),
		.csr_restore_dret_i(csr_restore_dret_id),
		.csr_save_cause_i(csr_save_cause),
		.csr_mcause_i(exc_cause),
		.csr_mtval_i(csr_mtval),
		.illegal_csr_insn_o(illegal_csr_insn_id),
		.double_fault_seen_o(double_fault_seen_o),
		.instr_ret_i(perf_instr_ret_wb),
		.instr_ret_compressed_i(perf_instr_ret_compressed_wb),
		.instr_ret_spec_i(perf_instr_ret_wb_spec),
		.instr_ret_compressed_spec_i(perf_instr_ret_compressed_wb_spec),
		.iside_wait_i(perf_iside_wait),
		.jump_i(perf_jump),
		.branch_i(perf_branch),
		.branch_taken_i(perf_tbranch),
		.mem_load_i(perf_load),
		.mem_store_i(perf_store),
		.dside_wait_i(perf_dside_wait),
		.mul_wait_i(perf_mul_wait),
		.div_wait_i(perf_div_wait)
	);
	generate
		if (PMPEnable) begin : g_pmp
			wire [31:0] pc_if_inc;
			wire [101:0] pmp_req_addr;
			wire [5:0] pmp_req_type;
			wire [5:0] pmp_priv_lvl;
			assign pc_if_inc = pc_if + 32'd2;
			assign pmp_req_addr[68+:34] = {2'b00, pc_if};
			assign pmp_req_type[4+:2] = 2'b00;
			assign pmp_priv_lvl[4+:2] = priv_mode_id;
			assign pmp_req_addr[34+:34] = {2'b00, pc_if_inc};
			assign pmp_req_type[2+:2] = 2'b00;
			assign pmp_priv_lvl[2+:2] = priv_mode_id;
			assign pmp_req_addr[0+:34] = {2'b00, data_addr_o[31:0]};
			assign pmp_req_type[0+:2] = (data_we_o ? 2'b01 : 2'b10);
			assign pmp_priv_lvl[0+:2] = priv_mode_lsu;
			ibex_pmp #(
				.PMPGranularity(PMPGranularity),
				.PMPNumChan(PMPNumChan),
				.PMPNumRegions(PMPNumRegions)
			) pmp_i(
				.csr_pmp_cfg_i(csr_pmp_cfg),
				.csr_pmp_addr_i(csr_pmp_addr),
				.csr_pmp_mseccfg_i(csr_pmp_mseccfg),
				.priv_mode_i(pmp_priv_lvl),
				.pmp_req_addr_i(pmp_req_addr),
				.pmp_req_type_i(pmp_req_type),
				.pmp_req_err_o(pmp_req_err)
			);
		end
		else begin : g_no_pmp
			wire [1:0] unused_priv_lvl_ls;
			wire [(PMPNumRegions * 34) - 1:0] unused_csr_pmp_addr;
			wire [(PMPNumRegions * 6) - 1:0] unused_csr_pmp_cfg;
			wire [2:0] unused_csr_pmp_mseccfg;
			assign unused_priv_lvl_ls = priv_mode_lsu;
			assign unused_csr_pmp_addr = csr_pmp_addr;
			assign unused_csr_pmp_cfg = csr_pmp_cfg;
			assign unused_csr_pmp_mseccfg = csr_pmp_mseccfg;
			assign pmp_req_err[ibex_pkg_PMP_I] = 1'b0;
			assign pmp_req_err[ibex_pkg_PMP_I2] = 1'b0;
			assign pmp_req_err[ibex_pkg_PMP_D] = 1'b0;
		end
	endgenerate
	wire unused_instr_new_id;
	wire unused_instr_id_done;
	wire unused_instr_done_wb;
	assign unused_instr_id_done = instr_id_done;
	assign unused_instr_new_id = instr_new_id;
	assign unused_instr_done_wb = instr_done_wb;
endmodule
module ibex_id_stage (
	clk_i,
	rst_ni,
	ctrl_busy_o,
	illegal_insn_o,
	instr_valid_i,
	instr_rdata_i,
	instr_rdata_alu_i,
	instr_rdata_c_i,
	instr_is_compressed_i,
	instr_bp_taken_i,
	instr_req_o,
	instr_first_cycle_id_o,
	instr_valid_clear_o,
	id_in_ready_o,
	instr_exec_i,
	icache_inval_o,
	branch_decision_i,
	pc_set_o,
	pc_mux_o,
	nt_branch_mispredict_o,
	nt_branch_addr_o,
	exc_pc_mux_o,
	exc_cause_o,
	illegal_c_insn_i,
	instr_fetch_err_i,
	instr_fetch_err_plus2_i,
	pc_id_i,
	ex_valid_i,
	lsu_resp_valid_i,
	alu_operator_ex_o,
	alu_operand_a_ex_o,
	alu_operand_b_ex_o,
	imd_val_we_ex_i,
	imd_val_d_ex_i,
	imd_val_q_ex_o,
	bt_a_operand_o,
	bt_b_operand_o,
	mult_en_ex_o,
	div_en_ex_o,
	mult_sel_ex_o,
	div_sel_ex_o,
	multdiv_operator_ex_o,
	multdiv_signed_mode_ex_o,
	multdiv_operand_a_ex_o,
	multdiv_operand_b_ex_o,
	multdiv_ready_id_o,
	csr_access_o,
	csr_op_o,
	csr_op_en_o,
	csr_save_if_o,
	csr_save_id_o,
	csr_save_wb_o,
	csr_restore_mret_id_o,
	csr_restore_dret_id_o,
	csr_save_cause_o,
	csr_mtval_o,
	priv_mode_i,
	csr_mstatus_tw_i,
	illegal_csr_insn_i,
	data_ind_timing_i,
	lsu_req_o,
	lsu_we_o,
	lsu_type_o,
	lsu_sign_ext_o,
	lsu_wdata_o,
	lsu_req_done_i,
	lsu_addr_incr_req_i,
	lsu_addr_last_i,
	csr_mstatus_mie_i,
	irq_pending_i,
	irqs_i,
	irq_nm_i,
	nmi_mode_o,
	lsu_load_err_i,
	lsu_load_resp_intg_err_i,
	lsu_store_err_i,
	lsu_store_resp_intg_err_i,
	debug_mode_o,
	debug_mode_entering_o,
	debug_cause_o,
	debug_csr_save_o,
	debug_req_i,
	debug_single_step_i,
	debug_ebreakm_i,
	debug_ebreaku_i,
	trigger_match_i,
	result_ex_i,
	csr_rdata_i,
	rf_raddr_a_o,
	rf_rdata_a_i,
	rf_raddr_b_o,
	rf_rdata_b_i,
	rf_ren_a_o,
	rf_ren_b_o,
	rf_waddr_id_o,
	rf_wdata_id_o,
	rf_we_id_o,
	rf_rd_a_wb_match_o,
	rf_rd_b_wb_match_o,
	rf_waddr_wb_i,
	rf_wdata_fwd_wb_i,
	rf_write_wb_i,
	en_wb_o,
	instr_type_wb_o,
	instr_perf_count_id_o,
	ready_wb_i,
	outstanding_load_wb_i,
	outstanding_store_wb_i,
	perf_jump_o,
	perf_branch_o,
	perf_tbranch_o,
	perf_dside_wait_o,
	perf_mul_wait_o,
	perf_div_wait_o,
	instr_id_done_o
);
	parameter [0:0] RV32E = 0;
	parameter integer RV32M = 32'sd2;
	parameter integer RV32B = 32'sd0;
	parameter [0:0] DataIndTiming = 1'b0;
	parameter [0:0] BranchTargetALU = 0;
	parameter [0:0] WritebackStage = 0;
	parameter [0:0] BranchPredictor = 0;
	parameter [0:0] MemECC = 1'b0;
	input wire clk_i;
	input wire rst_ni;
	output wire ctrl_busy_o;
	output wire illegal_insn_o;
	input wire instr_valid_i;
	input wire [31:0] instr_rdata_i;
	input wire [31:0] instr_rdata_alu_i;
	input wire [15:0] instr_rdata_c_i;
	input wire instr_is_compressed_i;
	input wire instr_bp_taken_i;
	output wire instr_req_o;
	output wire instr_first_cycle_id_o;
	output wire instr_valid_clear_o;
	output wire id_in_ready_o;
	input wire instr_exec_i;
	output wire icache_inval_o;
	input wire branch_decision_i;
	output wire pc_set_o;
	output wire [2:0] pc_mux_o;
	output wire nt_branch_mispredict_o;
	output wire [31:0] nt_branch_addr_o;
	output wire [1:0] exc_pc_mux_o;
	output wire [6:0] exc_cause_o;
	input wire illegal_c_insn_i;
	input wire instr_fetch_err_i;
	input wire instr_fetch_err_plus2_i;
	input wire [31:0] pc_id_i;
	input wire ex_valid_i;
	input wire lsu_resp_valid_i;
	output wire [6:0] alu_operator_ex_o;
	output wire [31:0] alu_operand_a_ex_o;
	output wire [31:0] alu_operand_b_ex_o;
	input wire [1:0] imd_val_we_ex_i;
	input wire [67:0] imd_val_d_ex_i;
	output wire [67:0] imd_val_q_ex_o;
	output reg [31:0] bt_a_operand_o;
	output reg [31:0] bt_b_operand_o;
	output wire mult_en_ex_o;
	output wire div_en_ex_o;
	output wire mult_sel_ex_o;
	output wire div_sel_ex_o;
	output wire [1:0] multdiv_operator_ex_o;
	output wire [1:0] multdiv_signed_mode_ex_o;
	output wire [31:0] multdiv_operand_a_ex_o;
	output wire [31:0] multdiv_operand_b_ex_o;
	output wire multdiv_ready_id_o;
	output wire csr_access_o;
	output wire [1:0] csr_op_o;
	output wire csr_op_en_o;
	output wire csr_save_if_o;
	output wire csr_save_id_o;
	output wire csr_save_wb_o;
	output wire csr_restore_mret_id_o;
	output wire csr_restore_dret_id_o;
	output wire csr_save_cause_o;
	output wire [31:0] csr_mtval_o;
	input wire [1:0] priv_mode_i;
	input wire csr_mstatus_tw_i;
	input wire illegal_csr_insn_i;
	input wire data_ind_timing_i;
	output wire lsu_req_o;
	output wire lsu_we_o;
	output wire [1:0] lsu_type_o;
	output wire lsu_sign_ext_o;
	output wire [31:0] lsu_wdata_o;
	input wire lsu_req_done_i;
	input wire lsu_addr_incr_req_i;
	input wire [31:0] lsu_addr_last_i;
	input wire csr_mstatus_mie_i;
	input wire irq_pending_i;
	input wire [17:0] irqs_i;
	input wire irq_nm_i;
	output wire nmi_mode_o;
	input wire lsu_load_err_i;
	input wire lsu_load_resp_intg_err_i;
	input wire lsu_store_err_i;
	input wire lsu_store_resp_intg_err_i;
	output wire debug_mode_o;
	output wire debug_mode_entering_o;
	output wire [2:0] debug_cause_o;
	output wire debug_csr_save_o;
	input wire debug_req_i;
	input wire debug_single_step_i;
	input wire debug_ebreakm_i;
	input wire debug_ebreaku_i;
	input wire trigger_match_i;
	input wire [31:0] result_ex_i;
	input wire [31:0] csr_rdata_i;
	output wire [4:0] rf_raddr_a_o;
	input wire [31:0] rf_rdata_a_i;
	output wire [4:0] rf_raddr_b_o;
	input wire [31:0] rf_rdata_b_i;
	output wire rf_ren_a_o;
	output wire rf_ren_b_o;
	output wire [4:0] rf_waddr_id_o;
	output reg [31:0] rf_wdata_id_o;
	output wire rf_we_id_o;
	output wire rf_rd_a_wb_match_o;
	output wire rf_rd_b_wb_match_o;
	input wire [4:0] rf_waddr_wb_i;
	input wire [31:0] rf_wdata_fwd_wb_i;
	input wire rf_write_wb_i;
	output wire en_wb_o;
	output wire [1:0] instr_type_wb_o;
	output wire instr_perf_count_id_o;
	input wire ready_wb_i;
	input wire outstanding_load_wb_i;
	input wire outstanding_store_wb_i;
	output wire perf_jump_o;
	output reg perf_branch_o;
	output wire perf_tbranch_o;
	output wire perf_dside_wait_o;
	output wire perf_mul_wait_o;
	output wire perf_div_wait_o;
	output wire instr_id_done_o;
	wire illegal_insn_dec;
	wire illegal_dret_insn;
	wire illegal_umode_insn;
	wire ebrk_insn;
	wire mret_insn_dec;
	wire dret_insn_dec;
	wire ecall_insn_dec;
	wire wfi_insn_dec;
	wire wb_exception;
	wire id_exception;
	wire branch_in_dec;
	wire branch_set;
	wire branch_set_raw;
	reg branch_set_raw_d;
	reg branch_jump_set_done_q;
	wire branch_jump_set_done_d;
	reg branch_not_set;
	wire branch_taken;
	wire jump_in_dec;
	wire jump_set_dec;
	wire jump_set;
	reg jump_set_raw;
	wire instr_first_cycle;
	wire instr_executing_spec;
	wire instr_executing;
	wire instr_done;
	wire controller_run;
	wire stall_ld_hz;
	wire stall_mem;
	reg stall_multdiv;
	reg stall_branch;
	reg stall_jump;
	wire stall_id;
	wire stall_wb;
	wire flush_id;
	wire multicycle_done;
	wire mem_resp_intg_err;
	wire [31:0] imm_i_type;
	wire [31:0] imm_s_type;
	wire [31:0] imm_b_type;
	wire [31:0] imm_u_type;
	wire [31:0] imm_j_type;
	wire [31:0] zimm_rs1_type;
	wire [31:0] imm_a;
	reg [31:0] imm_b;
	wire rf_wdata_sel;
	wire rf_we_dec;
	reg rf_we_raw;
	wire rf_ren_a;
	wire rf_ren_b;
	wire rf_ren_a_dec;
	wire rf_ren_b_dec;
	assign rf_ren_a = ((instr_valid_i & ~instr_fetch_err_i) & ~illegal_insn_o) & rf_ren_a_dec;
	assign rf_ren_b = ((instr_valid_i & ~instr_fetch_err_i) & ~illegal_insn_o) & rf_ren_b_dec;
	assign rf_ren_a_o = rf_ren_a;
	assign rf_ren_b_o = rf_ren_b;
	wire [31:0] rf_rdata_a_fwd;
	wire [31:0] rf_rdata_b_fwd;
	wire [6:0] alu_operator;
	wire [1:0] alu_op_a_mux_sel;
	wire [1:0] alu_op_a_mux_sel_dec;
	wire alu_op_b_mux_sel;
	wire alu_op_b_mux_sel_dec;
	wire alu_multicycle_dec;
	reg stall_alu;
	reg [67:0] imd_val_q;
	wire [1:0] bt_a_mux_sel;
	wire [2:0] bt_b_mux_sel;
	wire imm_a_mux_sel;
	wire [2:0] imm_b_mux_sel;
	wire [2:0] imm_b_mux_sel_dec;
	wire mult_en_id;
	wire mult_en_dec;
	wire div_en_id;
	wire div_en_dec;
	wire multdiv_en_dec;
	wire [1:0] multdiv_operator;
	wire [1:0] multdiv_signed_mode;
	wire lsu_we;
	wire [1:0] lsu_type;
	wire lsu_sign_ext;
	wire lsu_req;
	wire lsu_req_dec;
	wire data_req_allowed;
	reg csr_pipe_flush;
	reg [31:0] alu_operand_a;
	wire [31:0] alu_operand_b;
	assign alu_op_a_mux_sel = (lsu_addr_incr_req_i ? 2'd1 : alu_op_a_mux_sel_dec);
	assign alu_op_b_mux_sel = (lsu_addr_incr_req_i ? 1'd1 : alu_op_b_mux_sel_dec);
	assign imm_b_mux_sel = (lsu_addr_incr_req_i ? 3'd6 : imm_b_mux_sel_dec);
	assign imm_a = (imm_a_mux_sel == 1'd0 ? zimm_rs1_type : {32 {1'sb0}});
	always @(*) begin : alu_operand_a_mux
		case (alu_op_a_mux_sel)
			2'd0: alu_operand_a = rf_rdata_a_fwd;
			2'd1: alu_operand_a = lsu_addr_last_i;
			2'd2: alu_operand_a = pc_id_i;
			2'd3: alu_operand_a = imm_a;
			default: alu_operand_a = pc_id_i;
		endcase
	end
	generate
		if (BranchTargetALU) begin : g_btalu_muxes
			always @(*) begin : bt_operand_a_mux
				case (bt_a_mux_sel)
					2'd0: bt_a_operand_o = rf_rdata_a_fwd;
					2'd2: bt_a_operand_o = pc_id_i;
					default: bt_a_operand_o = pc_id_i;
				endcase
			end
			always @(*) begin : bt_immediate_b_mux
				case (bt_b_mux_sel)
					3'd0: bt_b_operand_o = imm_i_type;
					3'd2: bt_b_operand_o = imm_b_type;
					3'd4: bt_b_operand_o = imm_j_type;
					3'd5: bt_b_operand_o = (instr_is_compressed_i ? 32'h00000002 : 32'h00000004);
					default: bt_b_operand_o = (instr_is_compressed_i ? 32'h00000002 : 32'h00000004);
				endcase
			end
			always @(*) begin : immediate_b_mux
				case (imm_b_mux_sel)
					3'd0: imm_b = imm_i_type;
					3'd1: imm_b = imm_s_type;
					3'd3: imm_b = imm_u_type;
					3'd5: imm_b = (instr_is_compressed_i ? 32'h00000002 : 32'h00000004);
					3'd6: imm_b = 32'h00000004;
					default: imm_b = 32'h00000004;
				endcase
			end
		end
		else begin : g_nobtalu
			wire [1:0] unused_a_mux_sel;
			wire [2:0] unused_b_mux_sel;
			assign unused_a_mux_sel = bt_a_mux_sel;
			assign unused_b_mux_sel = bt_b_mux_sel;
			wire [32:1] sv2v_tmp_FACAA;
			assign sv2v_tmp_FACAA = 1'sb0;
			always @(*) bt_a_operand_o = sv2v_tmp_FACAA;
			wire [32:1] sv2v_tmp_A4AF9;
			assign sv2v_tmp_A4AF9 = 1'sb0;
			always @(*) bt_b_operand_o = sv2v_tmp_A4AF9;
			always @(*) begin : immediate_b_mux
				case (imm_b_mux_sel)
					3'd0: imm_b = imm_i_type;
					3'd1: imm_b = imm_s_type;
					3'd2: imm_b = imm_b_type;
					3'd3: imm_b = imm_u_type;
					3'd4: imm_b = imm_j_type;
					3'd5: imm_b = (instr_is_compressed_i ? 32'h00000002 : 32'h00000004);
					3'd6: imm_b = 32'h00000004;
					default: imm_b = 32'h00000004;
				endcase
			end
		end
	endgenerate
	assign alu_operand_b = (alu_op_b_mux_sel == 1'd1 ? imm_b : rf_rdata_b_fwd);
	genvar i;
	generate
		for (i = 0; i < 2; i = i + 1) begin : gen_intermediate_val_reg
			always @(posedge clk_i) begin : intermediate_val_reg
				if (!rst_ni)
					imd_val_q[(1 - i) * 34+:34] <= 1'sb0;
				else if (imd_val_we_ex_i[i])
					imd_val_q[(1 - i) * 34+:34] <= imd_val_d_ex_i[(1 - i) * 34+:34];
			end
		end
	endgenerate
	assign imd_val_q_ex_o = imd_val_q;
	assign rf_we_id_o = (rf_we_raw & instr_executing) & ~illegal_csr_insn_i;
	always @(*) begin : rf_wdata_id_mux
		case (rf_wdata_sel)
			1'd0: rf_wdata_id_o = result_ex_i;
			1'd1: rf_wdata_id_o = csr_rdata_i;
			default: rf_wdata_id_o = result_ex_i;
		endcase
	end
	ibex_decoder #(
		.RV32E(RV32E),
		.RV32M(RV32M),
		.RV32B(RV32B),
		.BranchTargetALU(BranchTargetALU)
	) decoder_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.illegal_insn_o(illegal_insn_dec),
		.ebrk_insn_o(ebrk_insn),
		.mret_insn_o(mret_insn_dec),
		.dret_insn_o(dret_insn_dec),
		.ecall_insn_o(ecall_insn_dec),
		.wfi_insn_o(wfi_insn_dec),
		.jump_set_o(jump_set_dec),
		.branch_taken_i(branch_taken),
		.icache_inval_o(icache_inval_o),
		.instr_first_cycle_i(instr_first_cycle),
		.instr_rdata_i(instr_rdata_i),
		.instr_rdata_alu_i(instr_rdata_alu_i),
		.illegal_c_insn_i(illegal_c_insn_i),
		.imm_a_mux_sel_o(imm_a_mux_sel),
		.imm_b_mux_sel_o(imm_b_mux_sel_dec),
		.bt_a_mux_sel_o(bt_a_mux_sel),
		.bt_b_mux_sel_o(bt_b_mux_sel),
		.imm_i_type_o(imm_i_type),
		.imm_s_type_o(imm_s_type),
		.imm_b_type_o(imm_b_type),
		.imm_u_type_o(imm_u_type),
		.imm_j_type_o(imm_j_type),
		.zimm_rs1_type_o(zimm_rs1_type),
		.rf_wdata_sel_o(rf_wdata_sel),
		.rf_we_o(rf_we_dec),
		.rf_raddr_a_o(rf_raddr_a_o),
		.rf_raddr_b_o(rf_raddr_b_o),
		.rf_waddr_o(rf_waddr_id_o),
		.rf_ren_a_o(rf_ren_a_dec),
		.rf_ren_b_o(rf_ren_b_dec),
		.alu_operator_o(alu_operator),
		.alu_op_a_mux_sel_o(alu_op_a_mux_sel_dec),
		.alu_op_b_mux_sel_o(alu_op_b_mux_sel_dec),
		.alu_multicycle_o(alu_multicycle_dec),
		.mult_en_o(mult_en_dec),
		.div_en_o(div_en_dec),
		.mult_sel_o(mult_sel_ex_o),
		.div_sel_o(div_sel_ex_o),
		.multdiv_operator_o(multdiv_operator),
		.multdiv_signed_mode_o(multdiv_signed_mode),
		.csr_access_o(csr_access_o),
		.csr_op_o(csr_op_o),
		.data_req_o(lsu_req_dec),
		.data_we_o(lsu_we),
		.data_type_o(lsu_type),
		.data_sign_extension_o(lsu_sign_ext),
		.jump_in_dec_o(jump_in_dec),
		.branch_in_dec_o(branch_in_dec)
	);
	always @(*) begin : csr_pipeline_flushes
		csr_pipe_flush = 1'b0;
		if ((csr_op_en_o == 1'b1) && ((csr_op_o == 2'd1) || (csr_op_o == 2'd2))) begin
			if ((((instr_rdata_i[31:20] == 12'h300) || (instr_rdata_i[31:20] == 12'h304)) || (instr_rdata_i[31:20] == 12'h747)) || (instr_rdata_i[31:25] == 7'h1d))
				csr_pipe_flush = 1'b1;
		end
		else if ((csr_op_en_o == 1'b1) && (csr_op_o != 2'd0)) begin
			if ((((instr_rdata_i[31:20] == 12'h7b0) || (instr_rdata_i[31:20] == 12'h7b1)) || (instr_rdata_i[31:20] == 12'h7b2)) || (instr_rdata_i[31:20] == 12'h7b3))
				csr_pipe_flush = 1'b1;
		end
	end
	assign illegal_dret_insn = dret_insn_dec & ~debug_mode_o;
	assign illegal_umode_insn = (priv_mode_i != 2'b11) & (mret_insn_dec | (csr_mstatus_tw_i & wfi_insn_dec));
	assign illegal_insn_o = instr_valid_i & (((illegal_insn_dec | illegal_csr_insn_i) | illegal_dret_insn) | illegal_umode_insn);
	assign mem_resp_intg_err = lsu_load_resp_intg_err_i | lsu_store_resp_intg_err_i;
	ibex_controller #(
		.WritebackStage(WritebackStage),
		.BranchPredictor(BranchPredictor),
		.MemECC(MemECC)
	) controller_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.ctrl_busy_o(ctrl_busy_o),
		.illegal_insn_i(illegal_insn_o),
		.ecall_insn_i(ecall_insn_dec),
		.mret_insn_i(mret_insn_dec),
		.dret_insn_i(dret_insn_dec),
		.wfi_insn_i(wfi_insn_dec),
		.ebrk_insn_i(ebrk_insn),
		.csr_pipe_flush_i(csr_pipe_flush),
		.instr_valid_i(instr_valid_i),
		.instr_i(instr_rdata_i),
		.instr_compressed_i(instr_rdata_c_i),
		.instr_is_compressed_i(instr_is_compressed_i),
		.instr_bp_taken_i(instr_bp_taken_i),
		.instr_fetch_err_i(instr_fetch_err_i),
		.instr_fetch_err_plus2_i(instr_fetch_err_plus2_i),
		.pc_id_i(pc_id_i),
		.instr_valid_clear_o(instr_valid_clear_o),
		.id_in_ready_o(id_in_ready_o),
		.controller_run_o(controller_run),
		.instr_exec_i(instr_exec_i),
		.instr_req_o(instr_req_o),
		.pc_set_o(pc_set_o),
		.pc_mux_o(pc_mux_o),
		.nt_branch_mispredict_o(nt_branch_mispredict_o),
		.exc_pc_mux_o(exc_pc_mux_o),
		.exc_cause_o(exc_cause_o),
		.lsu_addr_last_i(lsu_addr_last_i),
		.load_err_i(lsu_load_err_i),
		.mem_resp_intg_err_i(mem_resp_intg_err),
		.store_err_i(lsu_store_err_i),
		.wb_exception_o(wb_exception),
		.id_exception_o(id_exception),
		.branch_set_i(branch_set),
		.branch_not_set_i(branch_not_set),
		.jump_set_i(jump_set),
		.csr_mstatus_mie_i(csr_mstatus_mie_i),
		.irq_pending_i(irq_pending_i),
		.irqs_i(irqs_i),
		.irq_nm_ext_i(irq_nm_i),
		.nmi_mode_o(nmi_mode_o),
		.csr_save_if_o(csr_save_if_o),
		.csr_save_id_o(csr_save_id_o),
		.csr_save_wb_o(csr_save_wb_o),
		.csr_restore_mret_id_o(csr_restore_mret_id_o),
		.csr_restore_dret_id_o(csr_restore_dret_id_o),
		.csr_save_cause_o(csr_save_cause_o),
		.csr_mtval_o(csr_mtval_o),
		.priv_mode_i(priv_mode_i),
		.debug_mode_o(debug_mode_o),
		.debug_mode_entering_o(debug_mode_entering_o),
		.debug_cause_o(debug_cause_o),
		.debug_csr_save_o(debug_csr_save_o),
		.debug_req_i(debug_req_i),
		.debug_single_step_i(debug_single_step_i),
		.debug_ebreakm_i(debug_ebreakm_i),
		.debug_ebreaku_i(debug_ebreaku_i),
		.trigger_match_i(trigger_match_i),
		.stall_id_i(stall_id),
		.stall_wb_i(stall_wb),
		.flush_id_o(flush_id),
		.ready_wb_i(ready_wb_i),
		.perf_jump_o(perf_jump_o),
		.perf_tbranch_o(perf_tbranch_o)
	);
	assign multdiv_en_dec = mult_en_dec | div_en_dec;
	assign lsu_req = (instr_executing ? data_req_allowed & lsu_req_dec : 1'b0);
	assign mult_en_id = (instr_executing ? mult_en_dec : 1'b0);
	assign div_en_id = (instr_executing ? div_en_dec : 1'b0);
	assign lsu_req_o = lsu_req;
	assign lsu_we_o = lsu_we;
	assign lsu_type_o = lsu_type;
	assign lsu_sign_ext_o = lsu_sign_ext;
	assign lsu_wdata_o = rf_rdata_b_fwd;
	assign csr_op_en_o = (csr_access_o & instr_executing) & instr_id_done_o;
	assign alu_operator_ex_o = alu_operator;
	assign alu_operand_a_ex_o = alu_operand_a;
	assign alu_operand_b_ex_o = alu_operand_b;
	assign mult_en_ex_o = mult_en_id;
	assign div_en_ex_o = div_en_id;
	assign multdiv_operator_ex_o = multdiv_operator;
	assign multdiv_signed_mode_ex_o = multdiv_signed_mode;
	assign multdiv_operand_a_ex_o = rf_rdata_a_fwd;
	assign multdiv_operand_b_ex_o = rf_rdata_b_fwd;
	generate
		if (BranchTargetALU && !DataIndTiming) begin : g_branch_set_direct
			assign branch_set_raw = branch_set_raw_d;
		end
		else begin : g_branch_set_flop
			reg branch_set_raw_q;
			always @(posedge clk_i)
				if (!rst_ni)
					branch_set_raw_q <= 1'b0;
				else
					branch_set_raw_q <= branch_set_raw_d;
			assign branch_set_raw = (BranchTargetALU && !data_ind_timing_i ? branch_set_raw_d : branch_set_raw_q);
		end
	endgenerate
	assign branch_jump_set_done_d = ((branch_set_raw | jump_set_raw) | branch_jump_set_done_q) & ~instr_valid_clear_o;
	always @(posedge clk_i)
		if (!rst_ni)
			branch_jump_set_done_q <= 1'b0;
		else
			branch_jump_set_done_q <= branch_jump_set_done_d;
	assign jump_set = jump_set_raw & ~branch_jump_set_done_q;
	assign branch_set = branch_set_raw & ~branch_jump_set_done_q;
	generate
		if (DataIndTiming) begin : g_sec_branch_taken
			reg branch_taken_q;
			always @(posedge clk_i)
				if (!rst_ni)
					branch_taken_q <= 1'b0;
				else
					branch_taken_q <= branch_decision_i;
			assign branch_taken = ~data_ind_timing_i | branch_taken_q;
		end
		else begin : g_nosec_branch_taken
			assign branch_taken = 1'b1;
		end
		if (BranchPredictor) begin : g_calc_nt_addr
			assign nt_branch_addr_o = pc_id_i + (instr_is_compressed_i ? 32'd2 : 32'd4);
		end
		else begin : g_n_calc_nt_addr
			assign nt_branch_addr_o = 32'd0;
		end
	endgenerate
	reg id_fsm_q;
	reg id_fsm_d;
	always @(posedge clk_i) begin : id_pipeline_reg
		if (!rst_ni)
			id_fsm_q <= 1'd0;
		else if (instr_executing)
			id_fsm_q <= id_fsm_d;
	end
	always @(*) begin
		id_fsm_d = id_fsm_q;
		rf_we_raw = rf_we_dec;
		stall_multdiv = 1'b0;
		stall_jump = 1'b0;
		stall_branch = 1'b0;
		stall_alu = 1'b0;
		branch_set_raw_d = 1'b0;
		branch_not_set = 1'b0;
		jump_set_raw = 1'b0;
		perf_branch_o = 1'b0;
		if (instr_executing_spec)
			case (id_fsm_q)
				1'd0:
					case (1'b1)
						lsu_req_dec:
							if (!WritebackStage)
								id_fsm_d = 1'd1;
							else if (~lsu_req_done_i)
								id_fsm_d = 1'd1;
						multdiv_en_dec:
							if (~ex_valid_i) begin
								id_fsm_d = 1'd1;
								rf_we_raw = 1'b0;
								stall_multdiv = 1'b1;
							end
						branch_in_dec: begin
							id_fsm_d = (data_ind_timing_i || (!BranchTargetALU && branch_decision_i) ? 1'd1 : 1'd0);
							stall_branch = (~BranchTargetALU & branch_decision_i) | data_ind_timing_i;
							branch_set_raw_d = branch_decision_i | data_ind_timing_i;
							if (BranchPredictor)
								branch_not_set = ~branch_decision_i;
							perf_branch_o = 1'b1;
						end
						jump_in_dec: begin
							id_fsm_d = (BranchTargetALU ? 1'd0 : 1'd1);
							stall_jump = ~BranchTargetALU;
							jump_set_raw = jump_set_dec;
						end
						alu_multicycle_dec: begin
							stall_alu = 1'b1;
							id_fsm_d = 1'd1;
							rf_we_raw = 1'b0;
						end
						default: id_fsm_d = 1'd0;
					endcase
				1'd1: begin
					if (multdiv_en_dec)
						rf_we_raw = rf_we_dec & ex_valid_i;
					if (multicycle_done & ready_wb_i)
						id_fsm_d = 1'd0;
					else begin
						stall_multdiv = multdiv_en_dec;
						stall_branch = branch_in_dec;
						stall_jump = jump_in_dec;
					end
				end
				default: id_fsm_d = 1'd0;
			endcase
	end
	assign multdiv_ready_id_o = ready_wb_i;
	assign stall_id = ((((stall_ld_hz | stall_mem) | stall_multdiv) | stall_jump) | stall_branch) | stall_alu;
	assign instr_done = (~stall_id & ~flush_id) & instr_executing;
	assign instr_first_cycle = instr_valid_i & (id_fsm_q == 1'd0);
	assign instr_first_cycle_id_o = instr_first_cycle;
	generate
		if (WritebackStage) begin : gen_stall_mem
			wire rf_rd_a_wb_match;
			wire rf_rd_b_wb_match;
			wire rf_rd_a_hz;
			wire rf_rd_b_hz;
			wire outstanding_memory_access;
			wire instr_kill;
			assign multicycle_done = (lsu_req_dec ? ~stall_mem : ex_valid_i);
			assign outstanding_memory_access = (outstanding_load_wb_i | outstanding_store_wb_i) & ~lsu_resp_valid_i;
			assign data_req_allowed = ~outstanding_memory_access;
			assign instr_kill = ((instr_fetch_err_i | wb_exception) | id_exception) | ~controller_run;
			assign instr_executing_spec = ((instr_valid_i & ~instr_fetch_err_i) & controller_run) & ~stall_ld_hz;
			assign instr_executing = ((instr_valid_i & ~instr_kill) & ~stall_ld_hz) & ~outstanding_memory_access;
			assign stall_mem = instr_valid_i & (outstanding_memory_access | (lsu_req_dec & ~lsu_req_done_i));
			assign rf_rd_a_wb_match = (rf_waddr_wb_i == rf_raddr_a_o) & |rf_raddr_a_o;
			assign rf_rd_b_wb_match = (rf_waddr_wb_i == rf_raddr_b_o) & |rf_raddr_b_o;
			assign rf_rd_a_wb_match_o = rf_rd_a_wb_match;
			assign rf_rd_b_wb_match_o = rf_rd_b_wb_match;
			assign rf_rd_a_hz = rf_rd_a_wb_match & rf_ren_a;
			assign rf_rd_b_hz = rf_rd_b_wb_match & rf_ren_b;
			assign rf_rdata_a_fwd = (rf_rd_a_wb_match & rf_write_wb_i ? rf_wdata_fwd_wb_i : rf_rdata_a_i);
			assign rf_rdata_b_fwd = (rf_rd_b_wb_match & rf_write_wb_i ? rf_wdata_fwd_wb_i : rf_rdata_b_i);
			assign stall_ld_hz = outstanding_load_wb_i & (rf_rd_a_hz | rf_rd_b_hz);
			assign instr_type_wb_o = (~lsu_req_dec ? 2'd2 : (lsu_we ? 2'd1 : 2'd0));
			assign instr_id_done_o = en_wb_o & ready_wb_i;
			assign stall_wb = en_wb_o & ~ready_wb_i;
			assign perf_dside_wait_o = (instr_valid_i & ~instr_kill) & (outstanding_memory_access | stall_ld_hz);
		end
		else begin : gen_no_stall_mem
			assign multicycle_done = (lsu_req_dec ? lsu_resp_valid_i : ex_valid_i);
			assign data_req_allowed = instr_first_cycle;
			assign stall_mem = instr_valid_i & (lsu_req_dec & (~lsu_resp_valid_i | instr_first_cycle));
			assign stall_ld_hz = 1'b0;
			assign instr_executing_spec = (instr_valid_i & ~instr_fetch_err_i) & controller_run;
			assign instr_executing = instr_executing_spec;
			assign rf_rdata_a_fwd = rf_rdata_a_i;
			assign rf_rdata_b_fwd = rf_rdata_b_i;
			assign rf_rd_a_wb_match_o = 1'b0;
			assign rf_rd_b_wb_match_o = 1'b0;
			wire unused_data_req_done_ex;
			wire [4:0] unused_rf_waddr_wb;
			wire unused_rf_write_wb;
			wire unused_outstanding_load_wb;
			wire unused_outstanding_store_wb;
			wire unused_wb_exception;
			wire [31:0] unused_rf_wdata_fwd_wb;
			wire unused_id_exception;
			assign unused_data_req_done_ex = lsu_req_done_i;
			assign unused_rf_waddr_wb = rf_waddr_wb_i;
			assign unused_rf_write_wb = rf_write_wb_i;
			assign unused_outstanding_load_wb = outstanding_load_wb_i;
			assign unused_outstanding_store_wb = outstanding_store_wb_i;
			assign unused_wb_exception = wb_exception;
			assign unused_rf_wdata_fwd_wb = rf_wdata_fwd_wb_i;
			assign unused_id_exception = id_exception;
			assign instr_type_wb_o = 2'd2;
			assign stall_wb = 1'b0;
			assign perf_dside_wait_o = (instr_executing & lsu_req_dec) & ~lsu_resp_valid_i;
			assign instr_id_done_o = instr_done;
		end
	endgenerate
	assign instr_perf_count_id_o = (((~ebrk_insn & ~ecall_insn_dec) & ~illegal_insn_dec) & ~illegal_csr_insn_i) & ~instr_fetch_err_i;
	assign en_wb_o = instr_done;
	assign perf_mul_wait_o = stall_multdiv & mult_en_dec;
	assign perf_div_wait_o = stall_multdiv & div_en_dec;
endmodule
module ibex_alu (
	operator_i,
	operand_a_i,
	operand_b_i,
	instr_first_cycle_i,
	multdiv_operand_a_i,
	multdiv_operand_b_i,
	multdiv_sel_i,
	imd_val_q_i,
	imd_val_d_o,
	imd_val_we_o,
	adder_result_o,
	adder_result_ext_o,
	result_o,
	comparison_result_o,
	is_equal_result_o
);
	parameter integer RV32B = 32'sd0;
	input wire [6:0] operator_i;
	input wire [31:0] operand_a_i;
	input wire [31:0] operand_b_i;
	input wire instr_first_cycle_i;
	input wire [32:0] multdiv_operand_a_i;
	input wire [32:0] multdiv_operand_b_i;
	input wire multdiv_sel_i;
	input wire [63:0] imd_val_q_i;
	output reg [63:0] imd_val_d_o;
	output reg [1:0] imd_val_we_o;
	output wire [31:0] adder_result_o;
	output wire [33:0] adder_result_ext_o;
	output reg [31:0] result_o;
	output wire comparison_result_o;
	output wire is_equal_result_o;
	wire [31:0] operand_a_rev;
	wire [32:0] operand_b_neg;
	genvar k;
	generate
		for (k = 0; k < 32; k = k + 1) begin : gen_rev_operand_a
			assign operand_a_rev[k] = operand_a_i[31 - k];
		end
	endgenerate
	reg adder_op_a_shift1;
	reg adder_op_a_shift2;
	reg adder_op_a_shift3;
	reg adder_op_b_negate;
	reg [32:0] adder_in_a;
	reg [32:0] adder_in_b;
	wire [31:0] adder_result;
	always @(*) begin
		adder_op_a_shift1 = 1'b0;
		adder_op_a_shift2 = 1'b0;
		adder_op_a_shift3 = 1'b0;
		adder_op_b_negate = 1'b0;
		case (operator_i)
			7'd1, 7'd29, 7'd30, 7'd27, 7'd28, 7'd25, 7'd26, 7'd43, 7'd44, 7'd31, 7'd32, 7'd33, 7'd34: adder_op_b_negate = 1'b1;
			7'd22:
				if (RV32B != 32'sd0)
					adder_op_a_shift1 = 1'b1;
			7'd23:
				if (RV32B != 32'sd0)
					adder_op_a_shift2 = 1'b1;
			7'd24:
				if (RV32B != 32'sd0)
					adder_op_a_shift3 = 1'b1;
			default:
				;
		endcase
	end
	always @(*)
		case (1'b1)
			multdiv_sel_i: adder_in_a = multdiv_operand_a_i;
			adder_op_a_shift1: adder_in_a = {operand_a_i[30:0], 2'b01};
			adder_op_a_shift2: adder_in_a = {operand_a_i[29:0], 3'b001};
			adder_op_a_shift3: adder_in_a = {operand_a_i[28:0], 4'b0001};
			default: adder_in_a = {operand_a_i, 1'b1};
		endcase
	assign operand_b_neg = {operand_b_i, 1'b0} ^ {33 {1'b1}};
	always @(*)
		case (1'b1)
			multdiv_sel_i: adder_in_b = multdiv_operand_b_i;
			adder_op_b_negate: adder_in_b = operand_b_neg;
			default: adder_in_b = {operand_b_i, 1'b0};
		endcase
	assign adder_result_ext_o = $unsigned(adder_in_a) + $unsigned(adder_in_b);
	assign adder_result = adder_result_ext_o[32:1];
	assign adder_result_o = adder_result;
	wire is_equal;
	reg is_greater_equal;
	reg cmp_signed;
	always @(*)
		case (operator_i)
			7'd27, 7'd25, 7'd43, 7'd31, 7'd33: cmp_signed = 1'b1;
			default: cmp_signed = 1'b0;
		endcase
	assign is_equal = adder_result == 32'b00000000000000000000000000000000;
	assign is_equal_result_o = is_equal;
	always @(*)
		if ((operand_a_i[31] ^ operand_b_i[31]) == 1'b0)
			is_greater_equal = adder_result[31] == 1'b0;
		else
			is_greater_equal = operand_a_i[31] ^ cmp_signed;
	reg cmp_result;
	always @(*)
		case (operator_i)
			7'd29: cmp_result = is_equal;
			7'd30: cmp_result = ~is_equal;
			7'd27, 7'd28, 7'd33, 7'd34: cmp_result = is_greater_equal;
			7'd25, 7'd26, 7'd31, 7'd32, 7'd43, 7'd44: cmp_result = ~is_greater_equal;
			default: cmp_result = is_equal;
		endcase
	assign comparison_result_o = cmp_result;
	reg shift_left;
	wire shift_ones;
	wire shift_arith;
	wire shift_funnel;
	wire shift_sbmode;
	reg [5:0] shift_amt;
	wire [5:0] shift_amt_compl;
	reg [31:0] shift_operand;
	reg signed [32:0] shift_result_ext_signed;
	reg [32:0] shift_result_ext;
	reg unused_shift_result_ext;
	reg [31:0] shift_result;
	reg [31:0] shift_result_rev;
	wire bfp_op;
	wire [4:0] bfp_len;
	wire [4:0] bfp_off;
	wire [31:0] bfp_mask;
	wire [31:0] bfp_mask_rev;
	wire [31:0] bfp_result;
	assign bfp_op = (RV32B != 32'sd0 ? operator_i == 7'd55 : 1'b0);
	assign bfp_len = {~(|operand_b_i[27:24]), operand_b_i[27:24]};
	assign bfp_off = operand_b_i[20:16];
	assign bfp_mask = (RV32B != 32'sd0 ? ~(32'hffffffff << bfp_len) : {32 {1'sb0}});
	genvar i;
	generate
		for (i = 0; i < 32; i = i + 1) begin : gen_rev_bfp_mask
			assign bfp_mask_rev[i] = bfp_mask[31 - i];
		end
	endgenerate
	assign bfp_result = (RV32B != 32'sd0 ? (~shift_result & operand_a_i) | ((operand_b_i & bfp_mask) << bfp_off) : {32 {1'sb0}});
	wire [1:1] sv2v_tmp_3EBA5;
	assign sv2v_tmp_3EBA5 = operand_b_i[5] & shift_funnel;
	always @(*) shift_amt[5] = sv2v_tmp_3EBA5;
	assign shift_amt_compl = 32 - operand_b_i[4:0];
	always @(*)
		if (bfp_op)
			shift_amt[4:0] = bfp_off;
		else
			shift_amt[4:0] = (instr_first_cycle_i ? (operand_b_i[5] && shift_funnel ? shift_amt_compl[4:0] : operand_b_i[4:0]) : (operand_b_i[5] && shift_funnel ? operand_b_i[4:0] : shift_amt_compl[4:0]));
	assign shift_sbmode = (RV32B != 32'sd0 ? ((operator_i == 7'd49) | (operator_i == 7'd50)) | (operator_i == 7'd51) : 1'b0);
	always @(*) begin
		case (operator_i)
			7'd10: shift_left = 1'b1;
			7'd12: shift_left = ((RV32B == 32'sd2) || (RV32B == 32'sd3) ? 1'b1 : 1'b0);
			7'd55: shift_left = (RV32B != 32'sd0 ? 1'b1 : 1'b0);
			7'd14: shift_left = (RV32B != 32'sd0 ? instr_first_cycle_i : 0);
			7'd13: shift_left = (RV32B != 32'sd0 ? ~instr_first_cycle_i : 0);
			7'd47: shift_left = (RV32B != 32'sd0 ? (shift_amt[5] ? ~instr_first_cycle_i : instr_first_cycle_i) : 1'b0);
			7'd48: shift_left = (RV32B != 32'sd0 ? (shift_amt[5] ? instr_first_cycle_i : ~instr_first_cycle_i) : 1'b0);
			default: shift_left = 1'b0;
		endcase
		if (shift_sbmode)
			shift_left = 1'b1;
	end
	assign shift_arith = operator_i == 7'd8;
	assign shift_ones = ((RV32B == 32'sd2) || (RV32B == 32'sd3) ? (operator_i == 7'd12) | (operator_i == 7'd11) : 1'b0);
	assign shift_funnel = (RV32B != 32'sd0 ? (operator_i == 7'd47) | (operator_i == 7'd48) : 1'b0);
	always @(*) begin
		if (RV32B == 32'sd0)
			shift_operand = (shift_left ? operand_a_rev : operand_a_i);
		else
			case (1'b1)
				bfp_op: shift_operand = bfp_mask_rev;
				shift_sbmode: shift_operand = 32'h80000000;
				default: shift_operand = (shift_left ? operand_a_rev : operand_a_i);
			endcase
		shift_result_ext_signed = $signed({shift_ones | (shift_arith & shift_operand[31]), shift_operand}) >>> shift_amt[4:0];
		shift_result_ext = $unsigned(shift_result_ext_signed);
		shift_result = shift_result_ext[31:0];
		unused_shift_result_ext = shift_result_ext[32];
		begin : sv2v_autoblock_1
			reg [31:0] i;
			for (i = 0; i < 32; i = i + 1)
				shift_result_rev[i] = shift_result[31 - i];
		end
		shift_result = (shift_left ? shift_result_rev : shift_result);
	end
	wire bwlogic_or;
	wire bwlogic_and;
	wire [31:0] bwlogic_operand_b;
	wire [31:0] bwlogic_or_result;
	wire [31:0] bwlogic_and_result;
	wire [31:0] bwlogic_xor_result;
	reg [31:0] bwlogic_result;
	reg bwlogic_op_b_negate;
	always @(*)
		case (operator_i)
			7'd5, 7'd6, 7'd7: bwlogic_op_b_negate = (RV32B != 32'sd0 ? 1'b1 : 1'b0);
			7'd46: bwlogic_op_b_negate = (RV32B != 32'sd0 ? ~instr_first_cycle_i : 1'b0);
			default: bwlogic_op_b_negate = 1'b0;
		endcase
	assign bwlogic_operand_b = (bwlogic_op_b_negate ? operand_b_neg[32:1] : operand_b_i);
	assign bwlogic_or_result = operand_a_i | bwlogic_operand_b;
	assign bwlogic_and_result = operand_a_i & bwlogic_operand_b;
	assign bwlogic_xor_result = operand_a_i ^ bwlogic_operand_b;
	assign bwlogic_or = (operator_i == 7'd3) | (operator_i == 7'd6);
	assign bwlogic_and = (operator_i == 7'd4) | (operator_i == 7'd7);
	always @(*)
		case (1'b1)
			bwlogic_or: bwlogic_result = bwlogic_or_result;
			bwlogic_and: bwlogic_result = bwlogic_and_result;
			default: bwlogic_result = bwlogic_xor_result;
		endcase
	wire [5:0] bitcnt_result;
	wire [31:0] minmax_result;
	reg [31:0] pack_result;
	wire [31:0] sext_result;
	reg [31:0] singlebit_result;
	reg [31:0] rev_result;
	reg [31:0] shuffle_result;
	wire [31:0] xperm_result;
	reg [31:0] butterfly_result;
	reg [31:0] invbutterfly_result;
	reg [31:0] clmul_result;
	reg [31:0] multicycle_result;
	generate
		if (RV32B != 32'sd0) begin : g_alu_rvb
			wire zbe_op;
			wire bitcnt_ctz;
			wire bitcnt_clz;
			wire bitcnt_cz;
			reg [31:0] bitcnt_bits;
			wire [31:0] bitcnt_mask_op;
			reg [31:0] bitcnt_bit_mask;
			reg [191:0] bitcnt_partial;
			wire [31:0] bitcnt_partial_lsb_d;
			wire [31:0] bitcnt_partial_msb_d;
			assign bitcnt_ctz = operator_i == 7'd41;
			assign bitcnt_clz = operator_i == 7'd40;
			assign bitcnt_cz = bitcnt_ctz | bitcnt_clz;
			assign bitcnt_result = bitcnt_partial[0+:6];
			assign bitcnt_mask_op = (bitcnt_clz ? operand_a_rev : operand_a_i);
			always @(*) begin
				bitcnt_bit_mask = bitcnt_mask_op;
				bitcnt_bit_mask = bitcnt_bit_mask | (bitcnt_bit_mask << 1);
				bitcnt_bit_mask = bitcnt_bit_mask | (bitcnt_bit_mask << 2);
				bitcnt_bit_mask = bitcnt_bit_mask | (bitcnt_bit_mask << 4);
				bitcnt_bit_mask = bitcnt_bit_mask | (bitcnt_bit_mask << 8);
				bitcnt_bit_mask = bitcnt_bit_mask | (bitcnt_bit_mask << 16);
				bitcnt_bit_mask = ~bitcnt_bit_mask;
			end
			assign zbe_op = (operator_i == 7'd53) | (operator_i == 7'd54);
			always @(*)
				case (1'b1)
					zbe_op: bitcnt_bits = operand_b_i;
					bitcnt_cz: bitcnt_bits = bitcnt_bit_mask & ~bitcnt_mask_op;
					default: bitcnt_bits = operand_a_i;
				endcase
			always @(*) begin
				bitcnt_partial = {32 {6'b000000}};
				begin : sv2v_autoblock_2
					reg [31:0] i;
					for (i = 1; i < 32; i = i + 2)
						bitcnt_partial[(31 - i) * 6+:6] = {5'h00, bitcnt_bits[i]} + {5'h00, bitcnt_bits[i - 1]};
				end
				begin : sv2v_autoblock_3
					reg [31:0] i;
					for (i = 3; i < 32; i = i + 4)
						bitcnt_partial[(31 - i) * 6+:6] = bitcnt_partial[(33 - i) * 6+:6] + bitcnt_partial[(31 - i) * 6+:6];
				end
				begin : sv2v_autoblock_4
					reg [31:0] i;
					for (i = 7; i < 32; i = i + 8)
						bitcnt_partial[(31 - i) * 6+:6] = bitcnt_partial[(35 - i) * 6+:6] + bitcnt_partial[(31 - i) * 6+:6];
				end
				begin : sv2v_autoblock_5
					reg [31:0] i;
					for (i = 15; i < 32; i = i + 16)
						bitcnt_partial[(31 - i) * 6+:6] = bitcnt_partial[(39 - i) * 6+:6] + bitcnt_partial[(31 - i) * 6+:6];
				end
				bitcnt_partial[0+:6] = bitcnt_partial[96+:6] + bitcnt_partial[0+:6];
				bitcnt_partial[48+:6] = bitcnt_partial[96+:6] + bitcnt_partial[48+:6];
				begin : sv2v_autoblock_6
					reg [31:0] i;
					for (i = 11; i < 32; i = i + 8)
						bitcnt_partial[(31 - i) * 6+:6] = bitcnt_partial[(35 - i) * 6+:6] + bitcnt_partial[(31 - i) * 6+:6];
				end
				begin : sv2v_autoblock_7
					reg [31:0] i;
					for (i = 5; i < 32; i = i + 4)
						bitcnt_partial[(31 - i) * 6+:6] = bitcnt_partial[(33 - i) * 6+:6] + bitcnt_partial[(31 - i) * 6+:6];
				end
				bitcnt_partial[186+:6] = {5'h00, bitcnt_bits[0]};
				begin : sv2v_autoblock_8
					reg [31:0] i;
					for (i = 2; i < 32; i = i + 2)
						bitcnt_partial[(31 - i) * 6+:6] = bitcnt_partial[(32 - i) * 6+:6] + {5'h00, bitcnt_bits[i]};
				end
			end
			assign minmax_result = (cmp_result ? operand_a_i : operand_b_i);
			wire packu;
			wire packh;
			assign packu = operator_i == 7'd36;
			assign packh = operator_i == 7'd37;
			always @(*)
				case (1'b1)
					packu: pack_result = {operand_b_i[31:16], operand_a_i[31:16]};
					packh: pack_result = {16'h0000, operand_b_i[7:0], operand_a_i[7:0]};
					default: pack_result = {operand_b_i[15:0], operand_a_i[15:0]};
				endcase
			assign sext_result = (operator_i == 7'd38 ? {{24 {operand_a_i[7]}}, operand_a_i[7:0]} : {{16 {operand_a_i[15]}}, operand_a_i[15:0]});
			always @(*)
				case (operator_i)
					7'd49: singlebit_result = operand_a_i | shift_result;
					7'd50: singlebit_result = operand_a_i & ~shift_result;
					7'd51: singlebit_result = operand_a_i ^ shift_result;
					default: singlebit_result = {31'h00000000, shift_result[0]};
				endcase
			wire [4:0] zbp_shift_amt;
			wire gorc_op;
			assign gorc_op = operator_i == 7'd16;
			assign zbp_shift_amt[2:0] = ((RV32B == 32'sd2) || (RV32B == 32'sd3) ? shift_amt[2:0] : {3 {shift_amt[0]}});
			assign zbp_shift_amt[4:3] = ((RV32B == 32'sd2) || (RV32B == 32'sd3) ? shift_amt[4:3] : {2 {shift_amt[3]}});
			always @(*) begin
				rev_result = operand_a_i;
				if (zbp_shift_amt[0])
					rev_result = ((gorc_op ? rev_result : 32'h00000000) | ((rev_result & 32'h55555555) << 1)) | ((rev_result & 32'haaaaaaaa) >> 1);
				if (zbp_shift_amt[1])
					rev_result = ((gorc_op ? rev_result : 32'h00000000) | ((rev_result & 32'h33333333) << 2)) | ((rev_result & 32'hcccccccc) >> 2);
				if (zbp_shift_amt[2])
					rev_result = ((gorc_op ? rev_result : 32'h00000000) | ((rev_result & 32'h0f0f0f0f) << 4)) | ((rev_result & 32'hf0f0f0f0) >> 4);
				if (zbp_shift_amt[3])
					rev_result = ((((RV32B == 32'sd2) || (RV32B == 32'sd3)) && gorc_op ? rev_result : 32'h00000000) | ((rev_result & 32'h00ff00ff) << 8)) | ((rev_result & 32'hff00ff00) >> 8);
				if (zbp_shift_amt[4])
					rev_result = ((((RV32B == 32'sd2) || (RV32B == 32'sd3)) && gorc_op ? rev_result : 32'h00000000) | ((rev_result & 32'h0000ffff) << 16)) | ((rev_result & 32'hffff0000) >> 16);
			end
			wire crc_hmode;
			wire crc_bmode;
			wire [31:0] clmul_result_rev;
			if ((RV32B == 32'sd2) || (RV32B == 32'sd3)) begin : gen_alu_rvb_otearlgrey_full
				localparam [127:0] SHUFFLE_MASK_L = 128'h00ff00000f000f003030303044444444;
				localparam [127:0] SHUFFLE_MASK_R = 128'h0000ff0000f000f00c0c0c0c22222222;
				localparam [127:0] FLIP_MASK_L = 128'h22001100004400004411000011000000;
				localparam [127:0] FLIP_MASK_R = 128'h00880044000022000000882200000088;
				wire [31:0] SHUFFLE_MASK_NOT [0:3];
				genvar i;
				for (i = 0; i < 4; i = i + 1) begin : gen_shuffle_mask_not
					assign SHUFFLE_MASK_NOT[i] = ~(SHUFFLE_MASK_L[(3 - i) * 32+:32] | SHUFFLE_MASK_R[(3 - i) * 32+:32]);
				end
				wire shuffle_flip;
				assign shuffle_flip = operator_i == 7'd18;
				reg [3:0] shuffle_mode;
				always @(*) begin
					shuffle_result = operand_a_i;
					if (shuffle_flip) begin
						shuffle_mode[3] = shift_amt[0];
						shuffle_mode[2] = shift_amt[1];
						shuffle_mode[1] = shift_amt[2];
						shuffle_mode[0] = shift_amt[3];
					end
					else
						shuffle_mode = shift_amt[3:0];
					if (shuffle_flip)
						shuffle_result = ((((((((shuffle_result & 32'h88224411) | ((shuffle_result << 6) & FLIP_MASK_L[96+:32])) | ((shuffle_result >> 6) & FLIP_MASK_R[96+:32])) | ((shuffle_result << 9) & FLIP_MASK_L[64+:32])) | ((shuffle_result >> 9) & FLIP_MASK_R[64+:32])) | ((shuffle_result << 15) & FLIP_MASK_L[32+:32])) | ((shuffle_result >> 15) & FLIP_MASK_R[32+:32])) | ((shuffle_result << 21) & FLIP_MASK_L[0+:32])) | ((shuffle_result >> 21) & FLIP_MASK_R[0+:32]);
					if (shuffle_mode[3])
						shuffle_result = (shuffle_result & SHUFFLE_MASK_NOT[0]) | (((shuffle_result << 8) & SHUFFLE_MASK_L[96+:32]) | ((shuffle_result >> 8) & SHUFFLE_MASK_R[96+:32]));
					if (shuffle_mode[2])
						shuffle_result = (shuffle_result & SHUFFLE_MASK_NOT[1]) | (((shuffle_result << 4) & SHUFFLE_MASK_L[64+:32]) | ((shuffle_result >> 4) & SHUFFLE_MASK_R[64+:32]));
					if (shuffle_mode[1])
						shuffle_result = (shuffle_result & SHUFFLE_MASK_NOT[2]) | (((shuffle_result << 2) & SHUFFLE_MASK_L[32+:32]) | ((shuffle_result >> 2) & SHUFFLE_MASK_R[32+:32]));
					if (shuffle_mode[0])
						shuffle_result = (shuffle_result & SHUFFLE_MASK_NOT[3]) | (((shuffle_result << 1) & SHUFFLE_MASK_L[0+:32]) | ((shuffle_result >> 1) & SHUFFLE_MASK_R[0+:32]));
					if (shuffle_flip)
						shuffle_result = ((((((((shuffle_result & 32'h88224411) | ((shuffle_result << 6) & FLIP_MASK_L[96+:32])) | ((shuffle_result >> 6) & FLIP_MASK_R[96+:32])) | ((shuffle_result << 9) & FLIP_MASK_L[64+:32])) | ((shuffle_result >> 9) & FLIP_MASK_R[64+:32])) | ((shuffle_result << 15) & FLIP_MASK_L[32+:32])) | ((shuffle_result >> 15) & FLIP_MASK_R[32+:32])) | ((shuffle_result << 21) & FLIP_MASK_L[0+:32])) | ((shuffle_result >> 21) & FLIP_MASK_R[0+:32]);
				end
				wire [23:0] sel_n;
				wire [7:0] vld_n;
				wire [7:0] sel_b;
				wire [3:0] vld_b;
				wire [1:0] sel_h;
				wire [1:0] vld_h;
				for (i = 0; i < 8; i = i + 1) begin : gen_sel_vld_n
					assign sel_n[i * 3+:3] = operand_b_i[i * 4+:3];
					assign vld_n[i] = ~|operand_b_i[(i * 4) + 3+:1];
				end
				for (i = 0; i < 4; i = i + 1) begin : gen_sel_vld_b
					assign sel_b[i * 2+:2] = operand_b_i[i * 8+:2];
					assign vld_b[i] = ~|operand_b_i[(i * 8) + 2+:6];
				end
				for (i = 0; i < 2; i = i + 1) begin : gen_sel_vld_h
					assign sel_h[i+:1] = operand_b_i[i * 16+:1];
					assign vld_h[i] = ~|operand_b_i[(i * 16) + 1+:15];
				end
				reg [23:0] sel;
				reg [7:0] vld;
				always @(*)
					case (operator_i)
						7'd19: begin
							sel = sel_n;
							vld = vld_n;
						end
						7'd20: begin : sv2v_autoblock_9
							reg signed [31:0] b;
							for (b = 0; b < 4; b = b + 1)
								begin
									sel[((b * 2) + 0) * 3+:3] = {sel_b[b * 2+:2], 1'b0};
									sel[((b * 2) + 1) * 3+:3] = {sel_b[b * 2+:2], 1'b1};
									vld[b * 2+:2] = {2 {vld_b[b]}};
								end
						end
						7'd21: begin : sv2v_autoblock_10
							reg signed [31:0] h;
							for (h = 0; h < 2; h = h + 1)
								begin
									sel[((h * 4) + 0) * 3+:3] = {sel_h[h+:1], 2'b00};
									sel[((h * 4) + 1) * 3+:3] = {sel_h[h+:1], 2'b01};
									sel[((h * 4) + 2) * 3+:3] = {sel_h[h+:1], 2'b10};
									sel[((h * 4) + 3) * 3+:3] = {sel_h[h+:1], 2'b11};
									vld[h * 4+:4] = {4 {vld_h[h]}};
								end
						end
						default: begin
							sel = sel_n;
							vld = 1'sb0;
						end
					endcase
				wire [31:0] val_n;
				wire [31:0] xperm_n;
				assign val_n = operand_a_i;
				for (i = 0; i < 8; i = i + 1) begin : gen_xperm_n
					assign xperm_n[i * 4+:4] = (vld[i] ? val_n[sel[i * 3+:3] * 4+:4] : {4 {1'sb0}});
				end
				assign xperm_result = xperm_n;
				wire clmul_rmode;
				wire clmul_hmode;
				reg [31:0] clmul_op_a;
				reg [31:0] clmul_op_b;
				wire [31:0] operand_b_rev;
				wire [31:0] clmul_and_stage [0:31];
				wire [31:0] clmul_xor_stage1 [0:15];
				wire [31:0] clmul_xor_stage2 [0:7];
				wire [31:0] clmul_xor_stage3 [0:3];
				wire [31:0] clmul_xor_stage4 [0:1];
				wire [31:0] clmul_result_raw;
				for (i = 0; i < 32; i = i + 1) begin : gen_rev_operand_b
					assign operand_b_rev[i] = operand_b_i[31 - i];
				end
				assign clmul_rmode = operator_i == 7'd57;
				assign clmul_hmode = operator_i == 7'd58;
				localparam [31:0] CRC32_POLYNOMIAL = 32'h04c11db7;
				localparam [31:0] CRC32_MU_REV = 32'hf7011641;
				localparam [31:0] CRC32C_POLYNOMIAL = 32'h1edc6f41;
				localparam [31:0] CRC32C_MU_REV = 32'hdea713f1;
				wire crc_op;
				wire crc_cpoly;
				reg [31:0] crc_operand;
				wire [31:0] crc_poly;
				wire [31:0] crc_mu_rev;
				assign crc_op = (((((operator_i == 7'd64) | (operator_i == 7'd63)) | (operator_i == 7'd62)) | (operator_i == 7'd61)) | (operator_i == 7'd60)) | (operator_i == 7'd59);
				assign crc_cpoly = ((operator_i == 7'd64) | (operator_i == 7'd62)) | (operator_i == 7'd60);
				assign crc_hmode = (operator_i == 7'd61) | (operator_i == 7'd62);
				assign crc_bmode = (operator_i == 7'd59) | (operator_i == 7'd60);
				assign crc_poly = (crc_cpoly ? CRC32C_POLYNOMIAL : CRC32_POLYNOMIAL);
				assign crc_mu_rev = (crc_cpoly ? CRC32C_MU_REV : CRC32_MU_REV);
				always @(*)
					case (1'b1)
						crc_bmode: crc_operand = {operand_a_i[7:0], 24'h000000};
						crc_hmode: crc_operand = {operand_a_i[15:0], 16'h0000};
						default: crc_operand = operand_a_i;
					endcase
				always @(*)
					if (crc_op) begin
						clmul_op_a = (instr_first_cycle_i ? crc_operand : imd_val_q_i[32+:32]);
						clmul_op_b = (instr_first_cycle_i ? crc_mu_rev : crc_poly);
					end
					else begin
						clmul_op_a = (clmul_rmode | clmul_hmode ? operand_a_rev : operand_a_i);
						clmul_op_b = (clmul_rmode | clmul_hmode ? operand_b_rev : operand_b_i);
					end
				for (i = 0; i < 32; i = i + 1) begin : gen_clmul_and_op
					assign clmul_and_stage[i] = (clmul_op_b[i] ? clmul_op_a << i : {32 {1'sb0}});
				end
				for (i = 0; i < 16; i = i + 1) begin : gen_clmul_xor_op_l1
					assign clmul_xor_stage1[i] = clmul_and_stage[2 * i] ^ clmul_and_stage[(2 * i) + 1];
				end
				for (i = 0; i < 8; i = i + 1) begin : gen_clmul_xor_op_l2
					assign clmul_xor_stage2[i] = clmul_xor_stage1[2 * i] ^ clmul_xor_stage1[(2 * i) + 1];
				end
				for (i = 0; i < 4; i = i + 1) begin : gen_clmul_xor_op_l3
					assign clmul_xor_stage3[i] = clmul_xor_stage2[2 * i] ^ clmul_xor_stage2[(2 * i) + 1];
				end
				for (i = 0; i < 2; i = i + 1) begin : gen_clmul_xor_op_l4
					assign clmul_xor_stage4[i] = clmul_xor_stage3[2 * i] ^ clmul_xor_stage3[(2 * i) + 1];
				end
				assign clmul_result_raw = clmul_xor_stage4[0] ^ clmul_xor_stage4[1];
				for (i = 0; i < 32; i = i + 1) begin : gen_rev_clmul_result
					assign clmul_result_rev[i] = clmul_result_raw[31 - i];
				end
				always @(*)
					case (1'b1)
						clmul_rmode: clmul_result = clmul_result_rev;
						clmul_hmode: clmul_result = {1'b0, clmul_result_rev[31:1]};
						default: clmul_result = clmul_result_raw;
					endcase
			end
			else begin : gen_alu_rvb_not_otearlgrey_full
				wire [32:1] sv2v_tmp_F189D;
				assign sv2v_tmp_F189D = 1'sb0;
				always @(*) shuffle_result = sv2v_tmp_F189D;
				assign xperm_result = 1'sb0;
				wire [32:1] sv2v_tmp_B9A55;
				assign sv2v_tmp_B9A55 = 1'sb0;
				always @(*) clmul_result = sv2v_tmp_B9A55;
				assign clmul_result_rev = 1'sb0;
				assign crc_bmode = 1'sb0;
				assign crc_hmode = 1'sb0;
			end
			if (RV32B == 32'sd3) begin : gen_alu_rvb_full
				reg [191:0] bitcnt_partial_q;
				genvar i;
				for (i = 0; i < 32; i = i + 1) begin : gen_bitcnt_reg_in_lsb
					assign bitcnt_partial_lsb_d[i] = bitcnt_partial[(31 - i) * 6];
				end
				for (i = 0; i < 16; i = i + 1) begin : gen_bitcnt_reg_in_b1
					assign bitcnt_partial_msb_d[i] = bitcnt_partial[((31 - ((2 * i) + 1)) * 6) + 1];
				end
				for (i = 0; i < 8; i = i + 1) begin : gen_bitcnt_reg_in_b2
					assign bitcnt_partial_msb_d[16 + i] = bitcnt_partial[((31 - ((4 * i) + 3)) * 6) + 2];
				end
				for (i = 0; i < 4; i = i + 1) begin : gen_bitcnt_reg_in_b3
					assign bitcnt_partial_msb_d[24 + i] = bitcnt_partial[((31 - ((8 * i) + 7)) * 6) + 3];
				end
				for (i = 0; i < 2; i = i + 1) begin : gen_bitcnt_reg_in_b4
					assign bitcnt_partial_msb_d[28 + i] = bitcnt_partial[((31 - ((16 * i) + 15)) * 6) + 4];
				end
				assign bitcnt_partial_msb_d[30] = bitcnt_partial[5];
				assign bitcnt_partial_msb_d[31] = 1'b0;
				always @(*) begin
					bitcnt_partial_q = {32 {6'b000000}};
					begin : sv2v_autoblock_11
						reg [31:0] i;
						for (i = 0; i < 32; i = i + 1)
							begin : gen_bitcnt_reg_out_lsb
								bitcnt_partial_q[(31 - i) * 6] = imd_val_q_i[32 + i];
							end
					end
					begin : sv2v_autoblock_12
						reg [31:0] i;
						for (i = 0; i < 16; i = i + 1)
							begin : gen_bitcnt_reg_out_b1
								bitcnt_partial_q[((31 - ((2 * i) + 1)) * 6) + 1] = imd_val_q_i[0 + i];
							end
					end
					begin : sv2v_autoblock_13
						reg [31:0] i;
						for (i = 0; i < 8; i = i + 1)
							begin : gen_bitcnt_reg_out_b2
								bitcnt_partial_q[((31 - ((4 * i) + 3)) * 6) + 2] = imd_val_q_i[16 + i];
							end
					end
					begin : sv2v_autoblock_14
						reg [31:0] i;
						for (i = 0; i < 4; i = i + 1)
							begin : gen_bitcnt_reg_out_b3
								bitcnt_partial_q[((31 - ((8 * i) + 7)) * 6) + 3] = imd_val_q_i[24 + i];
							end
					end
					begin : sv2v_autoblock_15
						reg [31:0] i;
						for (i = 0; i < 2; i = i + 1)
							begin : gen_bitcnt_reg_out_b4
								bitcnt_partial_q[((31 - ((16 * i) + 15)) * 6) + 4] = imd_val_q_i[28 + i];
							end
					end
					bitcnt_partial_q[5] = imd_val_q_i[30];
				end
				wire [31:0] butterfly_mask_l [0:4];
				wire [31:0] butterfly_mask_r [0:4];
				wire [31:0] butterfly_mask_not [0:4];
				wire [31:0] lrotc_stage [0:4];
				genvar stg;
				for (stg = 0; stg < 5; stg = stg + 1) begin : gen_butterfly_ctrl_stage
					genvar seg;
					for (seg = 0; seg < (2 ** stg); seg = seg + 1) begin : gen_butterfly_ctrl
						assign lrotc_stage[stg][((2 * (16 >> stg)) * (seg + 1)) - 1:(2 * (16 >> stg)) * seg] = {{16 >> stg {1'b0}}, {16 >> stg {1'b1}}} << bitcnt_partial_q[((32 - ((16 >> stg) * ((2 * seg) + 1))) * 6) + ($clog2(16 >> stg) >= 0 ? $clog2(16 >> stg) : ($clog2(16 >> stg) + ($clog2(16 >> stg) >= 0 ? $clog2(16 >> stg) + 1 : 1 - $clog2(16 >> stg))) - 1)-:($clog2(16 >> stg) >= 0 ? $clog2(16 >> stg) + 1 : 1 - $clog2(16 >> stg))];
						assign butterfly_mask_l[stg][((16 >> stg) * ((2 * seg) + 2)) - 1:(16 >> stg) * ((2 * seg) + 1)] = ~lrotc_stage[stg][((16 >> stg) * ((2 * seg) + 2)) - 1:(16 >> stg) * ((2 * seg) + 1)];
						assign butterfly_mask_r[stg][((16 >> stg) * ((2 * seg) + 1)) - 1:(16 >> stg) * (2 * seg)] = ~lrotc_stage[stg][((16 >> stg) * ((2 * seg) + 2)) - 1:(16 >> stg) * ((2 * seg) + 1)];
						assign butterfly_mask_l[stg][((16 >> stg) * ((2 * seg) + 1)) - 1:(16 >> stg) * (2 * seg)] = 1'sb0;
						assign butterfly_mask_r[stg][((16 >> stg) * ((2 * seg) + 2)) - 1:(16 >> stg) * ((2 * seg) + 1)] = 1'sb0;
					end
				end
				for (stg = 0; stg < 5; stg = stg + 1) begin : gen_butterfly_not
					assign butterfly_mask_not[stg] = ~(butterfly_mask_l[stg] | butterfly_mask_r[stg]);
				end
				always @(*) begin
					butterfly_result = operand_a_i;
					butterfly_result = ((butterfly_result & butterfly_mask_not[0]) | ((butterfly_result & butterfly_mask_l[0]) >> 16)) | ((butterfly_result & butterfly_mask_r[0]) << 16);
					butterfly_result = ((butterfly_result & butterfly_mask_not[1]) | ((butterfly_result & butterfly_mask_l[1]) >> 8)) | ((butterfly_result & butterfly_mask_r[1]) << 8);
					butterfly_result = ((butterfly_result & butterfly_mask_not[2]) | ((butterfly_result & butterfly_mask_l[2]) >> 4)) | ((butterfly_result & butterfly_mask_r[2]) << 4);
					butterfly_result = ((butterfly_result & butterfly_mask_not[3]) | ((butterfly_result & butterfly_mask_l[3]) >> 2)) | ((butterfly_result & butterfly_mask_r[3]) << 2);
					butterfly_result = ((butterfly_result & butterfly_mask_not[4]) | ((butterfly_result & butterfly_mask_l[4]) >> 1)) | ((butterfly_result & butterfly_mask_r[4]) << 1);
					butterfly_result = butterfly_result & operand_b_i;
				end
				always @(*) begin
					invbutterfly_result = operand_a_i & operand_b_i;
					invbutterfly_result = ((invbutterfly_result & butterfly_mask_not[4]) | ((invbutterfly_result & butterfly_mask_l[4]) >> 1)) | ((invbutterfly_result & butterfly_mask_r[4]) << 1);
					invbutterfly_result = ((invbutterfly_result & butterfly_mask_not[3]) | ((invbutterfly_result & butterfly_mask_l[3]) >> 2)) | ((invbutterfly_result & butterfly_mask_r[3]) << 2);
					invbutterfly_result = ((invbutterfly_result & butterfly_mask_not[2]) | ((invbutterfly_result & butterfly_mask_l[2]) >> 4)) | ((invbutterfly_result & butterfly_mask_r[2]) << 4);
					invbutterfly_result = ((invbutterfly_result & butterfly_mask_not[1]) | ((invbutterfly_result & butterfly_mask_l[1]) >> 8)) | ((invbutterfly_result & butterfly_mask_r[1]) << 8);
					invbutterfly_result = ((invbutterfly_result & butterfly_mask_not[0]) | ((invbutterfly_result & butterfly_mask_l[0]) >> 16)) | ((invbutterfly_result & butterfly_mask_r[0]) << 16);
				end
			end
			else begin : gen_alu_rvb_not_full
				wire [31:0] unused_imd_val_q_1;
				assign unused_imd_val_q_1 = imd_val_q_i[0+:32];
				wire [32:1] sv2v_tmp_F770D;
				assign sv2v_tmp_F770D = 1'sb0;
				always @(*) butterfly_result = sv2v_tmp_F770D;
				wire [32:1] sv2v_tmp_02B8B;
				assign sv2v_tmp_02B8B = 1'sb0;
				always @(*) invbutterfly_result = sv2v_tmp_02B8B;
				assign bitcnt_partial_lsb_d = 1'sb0;
				assign bitcnt_partial_msb_d = 1'sb0;
			end
			always @(*)
				case (operator_i)
					7'd45: begin
						multicycle_result = (operand_b_i == 32'h00000000 ? operand_a_i : imd_val_q_i[32+:32]);
						imd_val_d_o = {operand_a_i, 32'h00000000};
						if (instr_first_cycle_i)
							imd_val_we_o = 2'b01;
						else
							imd_val_we_o = 2'b00;
					end
					7'd46: begin
						multicycle_result = imd_val_q_i[32+:32] | bwlogic_and_result;
						imd_val_d_o = {bwlogic_and_result, 32'h00000000};
						if (instr_first_cycle_i)
							imd_val_we_o = 2'b01;
						else
							imd_val_we_o = 2'b00;
					end
					7'd48, 7'd47, 7'd14, 7'd13: begin
						if (shift_amt[4:0] == 5'h00)
							multicycle_result = (shift_amt[5] ? operand_a_i : imd_val_q_i[32+:32]);
						else
							multicycle_result = imd_val_q_i[32+:32] | shift_result;
						imd_val_d_o = {shift_result, 32'h00000000};
						if (instr_first_cycle_i)
							imd_val_we_o = 2'b01;
						else
							imd_val_we_o = 2'b00;
					end
					7'd63, 7'd64, 7'd61, 7'd62, 7'd59, 7'd60:
						if ((RV32B == 32'sd2) || (RV32B == 32'sd3)) begin
							case (1'b1)
								crc_bmode: multicycle_result = clmul_result_rev ^ (operand_a_i >> 8);
								crc_hmode: multicycle_result = clmul_result_rev ^ (operand_a_i >> 16);
								default: multicycle_result = clmul_result_rev;
							endcase
							imd_val_d_o = {clmul_result_rev, 32'h00000000};
							if (instr_first_cycle_i)
								imd_val_we_o = 2'b01;
							else
								imd_val_we_o = 2'b00;
						end
						else begin
							imd_val_d_o = {operand_a_i, 32'h00000000};
							imd_val_we_o = 2'b00;
							multicycle_result = 1'sb0;
						end
					7'd53, 7'd54:
						if (RV32B == 32'sd3) begin
							multicycle_result = (operator_i == 7'd54 ? butterfly_result : invbutterfly_result);
							imd_val_d_o = {bitcnt_partial_lsb_d, bitcnt_partial_msb_d};
							if (instr_first_cycle_i)
								imd_val_we_o = 2'b11;
							else
								imd_val_we_o = 2'b00;
						end
						else begin
							imd_val_d_o = {operand_a_i, 32'h00000000};
							imd_val_we_o = 2'b00;
							multicycle_result = 1'sb0;
						end
					default: begin
						imd_val_d_o = {operand_a_i, 32'h00000000};
						imd_val_we_o = 2'b00;
						multicycle_result = 1'sb0;
					end
				endcase
		end
		else begin : g_no_alu_rvb
			wire [63:0] unused_imd_val_q;
			assign unused_imd_val_q = imd_val_q_i;
			wire [31:0] unused_butterfly_result;
			assign unused_butterfly_result = butterfly_result;
			wire [31:0] unused_invbutterfly_result;
			assign unused_invbutterfly_result = invbutterfly_result;
			assign bitcnt_result = 1'sb0;
			assign minmax_result = 1'sb0;
			wire [32:1] sv2v_tmp_B3EA0;
			assign sv2v_tmp_B3EA0 = 1'sb0;
			always @(*) pack_result = sv2v_tmp_B3EA0;
			assign sext_result = 1'sb0;
			wire [32:1] sv2v_tmp_C8829;
			assign sv2v_tmp_C8829 = 1'sb0;
			always @(*) singlebit_result = sv2v_tmp_C8829;
			wire [32:1] sv2v_tmp_F744D;
			assign sv2v_tmp_F744D = 1'sb0;
			always @(*) rev_result = sv2v_tmp_F744D;
			wire [32:1] sv2v_tmp_F189D;
			assign sv2v_tmp_F189D = 1'sb0;
			always @(*) shuffle_result = sv2v_tmp_F189D;
			assign xperm_result = 1'sb0;
			wire [32:1] sv2v_tmp_F770D;
			assign sv2v_tmp_F770D = 1'sb0;
			always @(*) butterfly_result = sv2v_tmp_F770D;
			wire [32:1] sv2v_tmp_02B8B;
			assign sv2v_tmp_02B8B = 1'sb0;
			always @(*) invbutterfly_result = sv2v_tmp_02B8B;
			wire [32:1] sv2v_tmp_B9A55;
			assign sv2v_tmp_B9A55 = 1'sb0;
			always @(*) clmul_result = sv2v_tmp_B9A55;
			wire [32:1] sv2v_tmp_8750A;
			assign sv2v_tmp_8750A = 1'sb0;
			always @(*) multicycle_result = sv2v_tmp_8750A;
			wire [64:1] sv2v_tmp_78BC2;
			assign sv2v_tmp_78BC2 = {2 {32'b00000000000000000000000000000000}};
			always @(*) imd_val_d_o = sv2v_tmp_78BC2;
			wire [2:1] sv2v_tmp_02FDF;
			assign sv2v_tmp_02FDF = {2 {1'b0}};
			always @(*) imd_val_we_o = sv2v_tmp_02FDF;
		end
	endgenerate
	always @(*) begin
		result_o = 1'sb0;
		case (operator_i)
			7'd2, 7'd5, 7'd3, 7'd6, 7'd4, 7'd7: result_o = bwlogic_result;
			7'd0, 7'd1, 7'd22, 7'd23, 7'd24: result_o = adder_result;
			7'd10, 7'd9, 7'd8, 7'd12, 7'd11: result_o = shift_result;
			7'd17, 7'd18: result_o = shuffle_result;
			7'd19, 7'd20, 7'd21: result_o = xperm_result;
			7'd29, 7'd30, 7'd27, 7'd28, 7'd25, 7'd26, 7'd43, 7'd44: result_o = {31'h00000000, cmp_result};
			7'd31, 7'd33, 7'd32, 7'd34: result_o = minmax_result;
			7'd40, 7'd41, 7'd42: result_o = {26'h0000000, bitcnt_result};
			7'd35, 7'd37, 7'd36: result_o = pack_result;
			7'd38, 7'd39: result_o = sext_result;
			7'd46, 7'd45, 7'd47, 7'd48, 7'd14, 7'd13, 7'd63, 7'd64, 7'd61, 7'd62, 7'd59, 7'd60, 7'd53, 7'd54: result_o = multicycle_result;
			7'd49, 7'd50, 7'd51, 7'd52: result_o = singlebit_result;
			7'd15, 7'd16: result_o = rev_result;
			7'd55: result_o = bfp_result;
			7'd56, 7'd57, 7'd58: result_o = clmul_result;
			default:
				;
		endcase
	end
	wire unused_shift_amt_compl;
	assign unused_shift_amt_compl = shift_amt_compl[5];
endmodule
module ibex_fetch_fifo (
	clk_i,
	rst_ni,
	clear_i,
	busy_o,
	in_valid_i,
	in_addr_i,
	in_rdata_i,
	in_err_i,
	out_valid_o,
	out_ready_i,
	out_addr_o,
	out_rdata_o,
	out_err_o,
	out_err_plus2_o
);
	parameter [31:0] NUM_REQS = 2;
	parameter [0:0] ResetAll = 1'b0;
	input wire clk_i;
	input wire rst_ni;
	input wire clear_i;
	output wire [NUM_REQS - 1:0] busy_o;
	input wire in_valid_i;
	input wire [31:0] in_addr_i;
	input wire [31:0] in_rdata_i;
	input wire in_err_i;
	output reg out_valid_o;
	input wire out_ready_i;
	output wire [31:0] out_addr_o;
	output reg [31:0] out_rdata_o;
	output reg out_err_o;
	output reg out_err_plus2_o;
	localparam [31:0] DEPTH = NUM_REQS + 1;
	wire [(DEPTH * 32) - 1:0] rdata_d;
	reg [(DEPTH * 32) - 1:0] rdata_q;
	wire [DEPTH - 1:0] err_d;
	reg [DEPTH - 1:0] err_q;
	wire [DEPTH - 1:0] valid_d;
	reg [DEPTH - 1:0] valid_q;
	wire [DEPTH - 1:0] lowest_free_entry;
	wire [DEPTH - 1:0] valid_pushed;
	wire [DEPTH - 1:0] valid_popped;
	wire [DEPTH - 1:0] entry_en;
	wire pop_fifo;
	wire [31:0] rdata;
	wire [31:0] rdata_unaligned;
	wire err;
	wire err_unaligned;
	wire err_plus2;
	wire valid;
	wire valid_unaligned;
	wire aligned_is_compressed;
	wire unaligned_is_compressed;
	wire addr_incr_two;
	wire [31:1] instr_addr_next;
	wire [31:1] instr_addr_d;
	reg [31:1] instr_addr_q;
	wire instr_addr_en;
	wire unused_addr_in;
	assign rdata = (valid_q[0] ? rdata_q[0+:32] : in_rdata_i);
	assign err = (valid_q[0] ? err_q[0] : in_err_i);
	assign valid = valid_q[0] | in_valid_i;
	assign rdata_unaligned = (valid_q[1] ? {rdata_q[47-:16], rdata[31:16]} : {in_rdata_i[15:0], rdata[31:16]});
	assign err_unaligned = (valid_q[1] ? (err_q[1] & ~unaligned_is_compressed) | err_q[0] : (valid_q[0] & err_q[0]) | (in_err_i & (~valid_q[0] | ~unaligned_is_compressed)));
	assign err_plus2 = (valid_q[1] ? err_q[1] & ~err_q[0] : (in_err_i & valid_q[0]) & ~err_q[0]);
	assign valid_unaligned = (valid_q[1] ? 1'b1 : valid_q[0] & in_valid_i);
	assign unaligned_is_compressed = (rdata[17:16] != 2'b11) & ~err;
	assign aligned_is_compressed = (rdata[1:0] != 2'b11) & ~err;
	always @(*)
		if (out_addr_o[1]) begin
			out_rdata_o = rdata_unaligned;
			out_err_o = err_unaligned;
			out_err_plus2_o = err_plus2;
			if (unaligned_is_compressed)
				out_valid_o = valid;
			else
				out_valid_o = valid_unaligned;
		end
		else begin
			out_rdata_o = rdata;
			out_err_o = err;
			out_err_plus2_o = 1'b0;
			out_valid_o = valid;
		end
	assign instr_addr_en = clear_i | (out_ready_i & out_valid_o);
	assign addr_incr_two = (instr_addr_q[1] ? unaligned_is_compressed : aligned_is_compressed);
	assign instr_addr_next = instr_addr_q[31:1] + {29'd0, ~addr_incr_two, addr_incr_two};
	assign instr_addr_d = (clear_i ? in_addr_i[31:1] : instr_addr_next);
	generate
		if (ResetAll) begin : g_instr_addr_ra
			always @(posedge clk_i)
				if (!rst_ni)
					instr_addr_q <= 1'sb0;
				else if (instr_addr_en)
					instr_addr_q <= instr_addr_d;
		end
		else begin : g_instr_addr_nr
			always @(posedge clk_i)
				if (instr_addr_en)
					instr_addr_q <= instr_addr_d;
		end
	endgenerate
	assign out_addr_o = {instr_addr_q, 1'b0};
	assign unused_addr_in = in_addr_i[0];
	assign busy_o = valid_q[DEPTH - 1:DEPTH - NUM_REQS];
	assign pop_fifo = (out_ready_i & out_valid_o) & (~aligned_is_compressed | out_addr_o[1]);
	genvar i;
	generate
		for (i = 0; i < (DEPTH - 1); i = i + 1) begin : g_fifo_next
			if (i == 0) begin : g_ent0
				assign lowest_free_entry[i] = ~valid_q[i];
			end
			else begin : g_ent_others
				assign lowest_free_entry[i] = ~valid_q[i] & valid_q[i - 1];
			end
			assign valid_pushed[i] = (in_valid_i & lowest_free_entry[i]) | valid_q[i];
			assign valid_popped[i] = (pop_fifo ? valid_pushed[i + 1] : valid_pushed[i]);
			assign valid_d[i] = valid_popped[i] & ~clear_i;
			assign entry_en[i] = (valid_pushed[i + 1] & pop_fifo) | ((in_valid_i & lowest_free_entry[i]) & ~pop_fifo);
			assign rdata_d[i * 32+:32] = (valid_q[i + 1] ? rdata_q[(i + 1) * 32+:32] : in_rdata_i);
			assign err_d[i] = (valid_q[i + 1] ? err_q[i + 1] : in_err_i);
		end
	endgenerate
	assign lowest_free_entry[DEPTH - 1] = ~valid_q[DEPTH - 1] & valid_q[DEPTH - 2];
	assign valid_pushed[DEPTH - 1] = valid_q[DEPTH - 1] | (in_valid_i & lowest_free_entry[DEPTH - 1]);
	assign valid_popped[DEPTH - 1] = (pop_fifo ? 1'b0 : valid_pushed[DEPTH - 1]);
	assign valid_d[DEPTH - 1] = valid_popped[DEPTH - 1] & ~clear_i;
	assign entry_en[DEPTH - 1] = in_valid_i & lowest_free_entry[DEPTH - 1];
	assign rdata_d[(DEPTH - 1) * 32+:32] = in_rdata_i;
	assign err_d[DEPTH - 1] = in_err_i;
	always @(posedge clk_i)
		if (!rst_ni)
			valid_q <= 1'sb0;
		else
			valid_q <= valid_d;
	generate
		for (i = 0; i < DEPTH; i = i + 1) begin : g_fifo_regs
			if (ResetAll) begin : g_rdata_ra
				always @(posedge clk_i)
					if (!rst_ni) begin
						rdata_q[i * 32+:32] <= 1'sb0;
						err_q[i] <= 1'sb0;
					end
					else if (entry_en[i]) begin
						rdata_q[i * 32+:32] <= rdata_d[i * 32+:32];
						err_q[i] <= err_d[i];
					end
			end
			else begin : g_rdata_nr
				always @(posedge clk_i)
					if (entry_en[i]) begin
						rdata_q[i * 32+:32] <= rdata_d[i * 32+:32];
						err_q[i] <= err_d[i];
					end
			end
		end
	endgenerate
endmodule
module ibex_counter (
	clk_i,
	rst_ni,
	counter_inc_i,
	counterh_we_i,
	counter_we_i,
	counter_val_i,
	counter_val_o,
	counter_val_upd_o
);
	parameter signed [31:0] CounterWidth = 32;
	parameter [0:0] ProvideValUpd = 0;
	input wire clk_i;
	input wire rst_ni;
	input wire counter_inc_i;
	input wire counterh_we_i;
	input wire counter_we_i;
	input wire [31:0] counter_val_i;
	output wire [63:0] counter_val_o;
	output wire [63:0] counter_val_upd_o;
	wire [63:0] counter;
	wire [CounterWidth - 1:0] counter_upd;
	reg [63:0] counter_load;
	reg we;
	reg [CounterWidth - 1:0] counter_d;
	assign counter_upd = counter[CounterWidth - 1:0] + {{CounterWidth - 1 {1'b0}}, 1'b1};
	always @(*) begin
		we = counter_we_i | counterh_we_i;
		counter_load[63:32] = counter[63:32];
		counter_load[31:0] = counter_val_i;
		if (counterh_we_i) begin
			counter_load[63:32] = counter_val_i;
			counter_load[31:0] = counter[31:0];
		end
		if (we)
			counter_d = counter_load[CounterWidth - 1:0];
		else if (counter_inc_i)
			counter_d = counter_upd[CounterWidth - 1:0];
		else
			counter_d = counter[CounterWidth - 1:0];
	end
	reg [CounterWidth - 1:0] counter_q;
	always @(posedge clk_i)
		if (!rst_ni)
			counter_q <= 1'sb0;
		else
			counter_q <= counter_d;
	generate
		if (CounterWidth < 64) begin : g_counter_narrow
			wire [63:CounterWidth] unused_counter_load;
			assign counter[CounterWidth - 1:0] = counter_q;
			assign counter[63:CounterWidth] = 1'sb0;
			if (ProvideValUpd) begin : g_counter_val_upd_o
				assign counter_val_upd_o[CounterWidth - 1:0] = counter_upd;
			end
			else begin : g_no_counter_val_upd_o
				assign counter_val_upd_o[CounterWidth - 1:0] = 1'sb0;
			end
			assign counter_val_upd_o[63:CounterWidth] = 1'sb0;
			assign unused_counter_load = counter_load[63:CounterWidth];
		end
		else begin : g_counter_full
			assign counter = counter_q;
			if (ProvideValUpd) begin : g_counter_val_upd_o
				assign counter_val_upd_o = counter_upd;
			end
			else begin : g_no_counter_val_upd_o
				assign counter_val_upd_o = 1'sb0;
			end
		end
	endgenerate
	assign counter_val_o = counter;
endmodule
module ibex_multdiv_slow (
	clk_i,
	rst_ni,
	mult_en_i,
	div_en_i,
	mult_sel_i,
	div_sel_i,
	operator_i,
	signed_mode_i,
	op_a_i,
	op_b_i,
	alu_adder_ext_i,
	alu_adder_i,
	equal_to_zero_i,
	data_ind_timing_i,
	alu_operand_a_o,
	alu_operand_b_o,
	imd_val_q_i,
	imd_val_d_o,
	imd_val_we_o,
	multdiv_ready_id_i,
	multdiv_result_o,
	valid_o
);
	input wire clk_i;
	input wire rst_ni;
	input wire mult_en_i;
	input wire div_en_i;
	input wire mult_sel_i;
	input wire div_sel_i;
	input wire [1:0] operator_i;
	input wire [1:0] signed_mode_i;
	input wire [31:0] op_a_i;
	input wire [31:0] op_b_i;
	input wire [33:0] alu_adder_ext_i;
	input wire [31:0] alu_adder_i;
	input wire equal_to_zero_i;
	input wire data_ind_timing_i;
	output reg [32:0] alu_operand_a_o;
	output reg [32:0] alu_operand_b_o;
	input wire [67:0] imd_val_q_i;
	output wire [67:0] imd_val_d_o;
	output wire [1:0] imd_val_we_o;
	input wire multdiv_ready_id_i;
	output wire [31:0] multdiv_result_o;
	output wire valid_o;
	reg [2:0] md_state_q;
	reg [2:0] md_state_d;
	wire [32:0] accum_window_q;
	reg [32:0] accum_window_d;
	wire unused_imd_val0;
	wire [1:0] unused_imd_val1;
	wire [32:0] res_adder_l;
	wire [32:0] res_adder_h;
	reg [4:0] multdiv_count_q;
	reg [4:0] multdiv_count_d;
	reg [32:0] op_b_shift_q;
	reg [32:0] op_b_shift_d;
	reg [32:0] op_a_shift_q;
	reg [32:0] op_a_shift_d;
	wire [32:0] op_a_ext;
	wire [32:0] op_b_ext;
	wire [32:0] one_shift;
	wire [32:0] op_a_bw_pp;
	wire [32:0] op_a_bw_last_pp;
	wire [31:0] b_0;
	wire sign_a;
	wire sign_b;
	wire [32:0] next_quotient;
	wire [31:0] next_remainder;
	wire [31:0] op_numerator_q;
	reg [31:0] op_numerator_d;
	wire is_greater_equal;
	wire div_change_sign;
	wire rem_change_sign;
	reg div_by_zero_d;
	reg div_by_zero_q;
	reg multdiv_hold;
	wire multdiv_en;
	assign res_adder_l = alu_adder_ext_i[32:0];
	assign res_adder_h = alu_adder_ext_i[33:1];
	assign imd_val_d_o[34+:34] = {1'b0, accum_window_d};
	assign imd_val_we_o[0] = ~multdiv_hold;
	assign accum_window_q = imd_val_q_i[66-:33];
	assign unused_imd_val0 = imd_val_q_i[67];
	assign imd_val_d_o[0+:34] = {2'b00, op_numerator_d};
	assign imd_val_we_o[1] = multdiv_en;
	assign op_numerator_q = imd_val_q_i[31-:32];
	assign unused_imd_val1 = imd_val_q_i[33-:2];
	always @(*) begin
		alu_operand_a_o = accum_window_q;
		case (operator_i)
			2'd0: alu_operand_b_o = op_a_bw_pp;
			2'd1: alu_operand_b_o = (md_state_q == 3'd4 ? op_a_bw_last_pp : op_a_bw_pp);
			2'd2, 2'd3:
				case (md_state_q)
					3'd0: begin
						alu_operand_a_o = 33'h000000001;
						alu_operand_b_o = {~op_b_i, 1'b1};
					end
					3'd1: begin
						alu_operand_a_o = 33'h000000001;
						alu_operand_b_o = {~op_a_i, 1'b1};
					end
					3'd2: begin
						alu_operand_a_o = 33'h000000001;
						alu_operand_b_o = {~op_b_i, 1'b1};
					end
					3'd5: begin
						alu_operand_a_o = 33'h000000001;
						alu_operand_b_o = {~accum_window_q[31:0], 1'b1};
					end
					default: begin
						alu_operand_a_o = {accum_window_q[31:0], 1'b1};
						alu_operand_b_o = {~op_b_shift_q[31:0], 1'b1};
					end
				endcase
			default: begin
				alu_operand_a_o = accum_window_q;
				alu_operand_b_o = {~op_b_shift_q[31:0], 1'b1};
			end
		endcase
	end
	assign b_0 = {32 {op_b_shift_q[0]}};
	assign op_a_bw_pp = {~(op_a_shift_q[32] & op_b_shift_q[0]), op_a_shift_q[31:0] & b_0};
	assign op_a_bw_last_pp = {op_a_shift_q[32] & op_b_shift_q[0], ~(op_a_shift_q[31:0] & b_0)};
	assign sign_a = op_a_i[31] & signed_mode_i[0];
	assign sign_b = op_b_i[31] & signed_mode_i[1];
	assign op_a_ext = {sign_a, op_a_i};
	assign op_b_ext = {sign_b, op_b_i};
	assign is_greater_equal = (accum_window_q[31] == op_b_shift_q[31] ? ~res_adder_h[31] : accum_window_q[31]);
	assign one_shift = 33'b000000000000000000000000000000001 << multdiv_count_q;
	assign next_remainder = (is_greater_equal ? res_adder_h[31:0] : accum_window_q[31:0]);
	assign next_quotient = (is_greater_equal ? op_a_shift_q | one_shift : op_a_shift_q);
	assign div_change_sign = (sign_a ^ sign_b) & ~div_by_zero_q;
	assign rem_change_sign = sign_a;
	always @(*) begin
		multdiv_count_d = multdiv_count_q;
		accum_window_d = accum_window_q;
		op_b_shift_d = op_b_shift_q;
		op_a_shift_d = op_a_shift_q;
		op_numerator_d = op_numerator_q;
		md_state_d = md_state_q;
		multdiv_hold = 1'b0;
		div_by_zero_d = div_by_zero_q;
		if (mult_sel_i || div_sel_i)
			case (md_state_q)
				3'd0: begin
					case (operator_i)
						2'd0: begin
							op_a_shift_d = op_a_ext << 1;
							accum_window_d = {~(op_a_ext[32] & op_b_i[0]), op_a_ext[31:0] & {32 {op_b_i[0]}}};
							op_b_shift_d = op_b_ext >> 1;
							md_state_d = (!data_ind_timing_i && ((op_b_ext >> 1) == 0) ? 3'd4 : 3'd3);
						end
						2'd1: begin
							op_a_shift_d = op_a_ext;
							accum_window_d = {1'b1, ~(op_a_ext[32] & op_b_i[0]), op_a_ext[31:1] & {31 {op_b_i[0]}}};
							op_b_shift_d = op_b_ext >> 1;
							md_state_d = 3'd3;
						end
						2'd2: begin
							accum_window_d = {33 {1'b1}};
							md_state_d = (!data_ind_timing_i && equal_to_zero_i ? 3'd6 : 3'd1);
							div_by_zero_d = equal_to_zero_i;
						end
						2'd3: begin
							accum_window_d = op_a_ext;
							md_state_d = (!data_ind_timing_i && equal_to_zero_i ? 3'd6 : 3'd1);
						end
						default:
							;
					endcase
					multdiv_count_d = 5'd31;
				end
				3'd1: begin
					op_a_shift_d = 1'sb0;
					op_numerator_d = (sign_a ? alu_adder_i : op_a_i);
					md_state_d = 3'd2;
				end
				3'd2: begin
					accum_window_d = {32'h00000000, op_numerator_q[31]};
					op_b_shift_d = (sign_b ? {1'b0, alu_adder_i} : {1'b0, op_b_i});
					md_state_d = 3'd3;
				end
				3'd3: begin
					multdiv_count_d = multdiv_count_q - 5'h01;
					case (operator_i)
						2'd0: begin
							accum_window_d = res_adder_l;
							op_a_shift_d = op_a_shift_q << 1;
							op_b_shift_d = op_b_shift_q >> 1;
							md_state_d = ((!data_ind_timing_i && (op_b_shift_d == 0)) || (multdiv_count_q == 5'd1) ? 3'd4 : 3'd3);
						end
						2'd1: begin
							accum_window_d = res_adder_h;
							op_a_shift_d = op_a_shift_q;
							op_b_shift_d = op_b_shift_q >> 1;
							md_state_d = (multdiv_count_q == 5'd1 ? 3'd4 : 3'd3);
						end
						2'd2, 2'd3: begin
							accum_window_d = {next_remainder[31:0], op_numerator_q[multdiv_count_d]};
							op_a_shift_d = next_quotient;
							md_state_d = (multdiv_count_q == 5'd1 ? 3'd4 : 3'd3);
						end
						default:
							;
					endcase
				end
				3'd4:
					case (operator_i)
						2'd0: begin
							accum_window_d = res_adder_l;
							md_state_d = 3'd0;
							multdiv_hold = ~multdiv_ready_id_i;
						end
						2'd1: begin
							accum_window_d = res_adder_l;
							md_state_d = 3'd0;
							md_state_d = 3'd0;
							multdiv_hold = ~multdiv_ready_id_i;
						end
						2'd2: begin
							accum_window_d = next_quotient;
							md_state_d = 3'd5;
						end
						2'd3: begin
							accum_window_d = {1'b0, next_remainder[31:0]};
							md_state_d = 3'd5;
						end
						default:
							;
					endcase
				3'd5: begin
					md_state_d = 3'd6;
					case (operator_i)
						2'd2: accum_window_d = (div_change_sign ? {1'b0, alu_adder_i} : accum_window_q);
						2'd3: accum_window_d = (rem_change_sign ? {1'b0, alu_adder_i} : accum_window_q);
						default:
							;
					endcase
				end
				3'd6: begin
					md_state_d = 3'd0;
					multdiv_hold = ~multdiv_ready_id_i;
				end
				default: md_state_d = 3'd0;
			endcase
	end
	assign multdiv_en = (mult_en_i | div_en_i) & ~multdiv_hold;
	always @(posedge clk_i)
		if (!rst_ni) begin
			multdiv_count_q <= 5'h00;
			op_b_shift_q <= 33'h000000000;
			op_a_shift_q <= 33'h000000000;
			md_state_q <= 3'd0;
			div_by_zero_q <= 1'b0;
		end
		else if (multdiv_en) begin
			multdiv_count_q <= multdiv_count_d;
			op_b_shift_q <= op_b_shift_d;
			op_a_shift_q <= op_a_shift_d;
			md_state_q <= md_state_d;
			div_by_zero_q <= div_by_zero_d;
		end
	assign valid_o = (md_state_q == 3'd6) | ((md_state_q == 3'd4) & ((operator_i == 2'd0) | (operator_i == 2'd1)));
	assign multdiv_result_o = (div_en_i ? accum_window_q[31:0] : res_adder_l[31:0]);
endmodule
module ibex_dummy_instr (
	clk_i,
	rst_ni,
	dummy_instr_en_i,
	dummy_instr_mask_i,
	dummy_instr_seed_en_i,
	dummy_instr_seed_i,
	fetch_valid_i,
	id_in_ready_i,
	insert_dummy_instr_o,
	dummy_instr_data_o
);
	localparam signed [31:0] ibex_pkg_LfsrWidth = 32;
	localparam [31:0] ibex_pkg_RndCnstLfsrSeedDefault = 32'hac533bf4;
	parameter [31:0] RndCnstLfsrSeed = ibex_pkg_RndCnstLfsrSeedDefault;
	localparam [159:0] ibex_pkg_RndCnstLfsrPermDefault = 160'h1e35ecba467fd1b12e958152c04fa43878a8daed;
	parameter [159:0] RndCnstLfsrPerm = ibex_pkg_RndCnstLfsrPermDefault;
	input wire clk_i;
	input wire rst_ni;
	input wire dummy_instr_en_i;
	input wire [2:0] dummy_instr_mask_i;
	input wire dummy_instr_seed_en_i;
	input wire [31:0] dummy_instr_seed_i;
	input wire fetch_valid_i;
	input wire id_in_ready_i;
	output wire insert_dummy_instr_o;
	output wire [31:0] dummy_instr_data_o;
	localparam [31:0] TIMEOUT_CNT_W = 5;
	localparam [31:0] OP_W = 5;
	localparam [31:0] LFSR_OUT_W = 17;
	wire [16:0] lfsr_data;
	wire [4:0] dummy_cnt_incr;
	wire [4:0] dummy_cnt_threshold;
	wire [4:0] dummy_cnt_d;
	reg [4:0] dummy_cnt_q;
	wire dummy_cnt_en;
	wire lfsr_en;
	wire [16:0] lfsr_state;
	wire insert_dummy_instr;
	reg [6:0] dummy_set;
	reg [2:0] dummy_opcode;
	wire [31:0] dummy_instr;
	reg [31:0] dummy_instr_seed_q;
	wire [31:0] dummy_instr_seed_d;
	assign lfsr_en = insert_dummy_instr & id_in_ready_i;
	assign dummy_instr_seed_d = dummy_instr_seed_q ^ dummy_instr_seed_i;
	always @(posedge clk_i)
		if (!rst_ni)
			dummy_instr_seed_q <= 1'sb0;
		else if (dummy_instr_seed_en_i)
			dummy_instr_seed_q <= dummy_instr_seed_d;
	prim_lfsr #(
		.LfsrDw(ibex_pkg_LfsrWidth),
		.StateOutDw(LFSR_OUT_W),
		.DefaultSeed(RndCnstLfsrSeed),
		.StatePermEn(1'b1),
		.StatePerm(RndCnstLfsrPerm)
	) lfsr_i(
		.clk_i(clk_i),
		.rst_ni(rst_ni),
		.seed_en_i(dummy_instr_seed_en_i),
		.seed_i(dummy_instr_seed_d),
		.lfsr_en_i(lfsr_en),
		.entropy_i(1'sb0),
		.state_o(lfsr_state)
	);
	function automatic [16:0] sv2v_cast_A20E1;
		input reg [16:0] inp;
		sv2v_cast_A20E1 = inp;
	endfunction
	assign lfsr_data = sv2v_cast_A20E1(lfsr_state);
	assign dummy_cnt_threshold = lfsr_data[4-:TIMEOUT_CNT_W] & {dummy_instr_mask_i, {2 {1'b1}}};
	assign dummy_cnt_incr = dummy_cnt_q + {{4 {1'b0}}, 1'b1};
	assign dummy_cnt_d = (insert_dummy_instr ? {5 {1'sb0}} : dummy_cnt_incr);
	assign dummy_cnt_en = (dummy_instr_en_i & id_in_ready_i) & (fetch_valid_i | insert_dummy_instr);
	always @(posedge clk_i)
		if (!rst_ni)
			dummy_cnt_q <= 1'sb0;
		else if (dummy_cnt_en)
			dummy_cnt_q <= dummy_cnt_d;
	assign insert_dummy_instr = dummy_instr_en_i & (dummy_cnt_q == dummy_cnt_threshold);
	always @(*)
		case (lfsr_data[16-:2])
			2'b00: begin
				dummy_set = 7'b0000000;
				dummy_opcode = 3'b000;
			end
			2'b01: begin
				dummy_set = 7'b0000001;
				dummy_opcode = 3'b000;
			end
			2'b10: begin
				dummy_set = 7'b0000001;
				dummy_opcode = 3'b100;
			end
			2'b11: begin
				dummy_set = 7'b0000000;
				dummy_opcode = 3'b111;
			end
			default: begin
				dummy_set = 7'b0000000;
				dummy_opcode = 3'b000;
			end
		endcase
	assign dummy_instr = {dummy_set, lfsr_data[14-:5], lfsr_data[9-:5], dummy_opcode, 12'h033};
	assign insert_dummy_instr_o = insert_dummy_instr;
	assign dummy_instr_data_o = dummy_instr;
endmodule
module ibex_top (
	clk_i,
	rst_ni,
	test_en_i,
	ram_cfg_i,
	hart_id_i,
	boot_addr_i,
	instr_req_o,
	instr_gnt_i,
	instr_rvalid_i,
	instr_addr_o,
	instr_rdata_i,
	instr_rdata_intg_i,
	instr_err_i,
	data_req_o,
	data_gnt_i,
	data_rvalid_i,
	data_we_o,
	data_be_o,
	data_addr_o,
	data_wdata_o,
	data_wdata_intg_o,
	data_rdata_i,
	data_rdata_intg_i,
	data_err_i,
	irq_software_i,
	irq_timer_i,
	irq_external_i,
	irq_fast_i,
	irq_nm_i,
	scramble_key_valid_i,
	scramble_key_i,
	scramble_nonce_i,
	scramble_req_o,
	debug_req_i,
	crash_dump_o,
	double_fault_seen_o,
	fetch_enable_i,
	alert_minor_o,
	alert_major_internal_o,
	alert_major_bus_o,
	core_sleep_o,
	scan_rst_ni
);
	parameter [0:0] PMPEnable = 1'b0;
	parameter [31:0] PMPGranularity = 0;
	parameter [31:0] PMPNumRegions = 4;
	parameter [31:0] MHPMCounterNum = 0;
	parameter [31:0] MHPMCounterWidth = 40;
	parameter [0:0] RV32E = 1'b0;
	parameter integer RV32M = 32'sd2;
	parameter integer RV32B = 32'sd0;
	parameter integer RegFile = 32'sd0;
	parameter [0:0] BranchTargetALU = 1'b0;
	parameter [0:0] WritebackStage = 1'b0;
	parameter [0:0] ICache = 1'b0;
	parameter [0:0] ICacheECC = 1'b0;
	parameter [0:0] BranchPredictor = 1'b0;
	parameter [0:0] DbgTriggerEn = 1'b0;
	parameter [31:0] DbgHwBreakNum = 1;
	parameter [0:0] SecureIbex = 1'b0;
	parameter [0:0] ICacheScramble = 1'b0;
	localparam signed [31:0] ibex_pkg_LfsrWidth = 32;
	localparam [31:0] ibex_pkg_RndCnstLfsrSeedDefault = 32'hac533bf4;
	parameter [31:0] RndCnstLfsrSeed = ibex_pkg_RndCnstLfsrSeedDefault;
	localparam [159:0] ibex_pkg_RndCnstLfsrPermDefault = 160'h1e35ecba467fd1b12e958152c04fa43878a8daed;
	parameter [159:0] RndCnstLfsrPerm = ibex_pkg_RndCnstLfsrPermDefault;
	parameter [31:0] DmHaltAddr = 32'h1a110800;
	parameter [31:0] DmExceptionAddr = 32'h1a110808;
	localparam [31:0] ibex_pkg_SCRAMBLE_KEY_W = 128;
	localparam [127:0] ibex_pkg_RndCnstIbexKeyDefault = 128'h14e8cecae3040d5e12286bb3cc113298;
	parameter [127:0] RndCnstIbexKey = ibex_pkg_RndCnstIbexKeyDefault;
	localparam [31:0] ibex_pkg_SCRAMBLE_NONCE_W = 64;
	localparam [63:0] ibex_pkg_RndCnstIbexNonceDefault = 64'hf79780bc735f3843;
	parameter [63:0] RndCnstIbexNonce = ibex_pkg_RndCnstIbexNonceDefault;
	parameter [0:0] ResetAllOnStart = 1'b0;
	input wire clk_i;
	input wire rst_ni;
	input wire test_en_i;
	input wire [9:0] ram_cfg_i;
	input wire [31:0] hart_id_i;
	input wire [31:0] boot_addr_i;
	output wire instr_req_o;
	input wire instr_gnt_i;
	input wire instr_rvalid_i;
	output wire [31:0] instr_addr_o;
	input wire [31:0] instr_rdata_i;
	input wire [6:0] instr_rdata_intg_i;
	input wire instr_err_i;
	output wire data_req_o;
	input wire data_gnt_i;
	input wire data_rvalid_i;
	output wire data_we_o;
	output wire [3:0] data_be_o;
	output wire [31:0] data_addr_o;
	output wire [31:0] data_wdata_o;
	output wire [6:0] data_wdata_intg_o;
	input wire [31:0] data_rdata_i;
	input wire [6:0] data_rdata_intg_i;
	input wire data_err_i;
	input wire irq_software_i;
	input wire irq_timer_i;
	input wire irq_external_i;
	input wire [14:0] irq_fast_i;
	input wire irq_nm_i;
	input wire scramble_key_valid_i;
	input wire [127:0] scramble_key_i;
	input wire [63:0] scramble_nonce_i;
	output wire scramble_req_o;
	input wire debug_req_i;
	output wire [159:0] crash_dump_o;
	output wire double_fault_seen_o;
	input wire [3:0] fetch_enable_i;
	output wire alert_minor_o;
	output wire alert_major_internal_o;
	output wire alert_major_bus_o;
	output wire core_sleep_o;
	input wire scan_rst_ni;
	localparam [0:0] Lockstep = SecureIbex;
	localparam [0:0] ResetAll = Lockstep || ResetAllOnStart;
	localparam [0:0] DummyInstructions = SecureIbex;
	localparam [0:0] RegFileECC = SecureIbex;
	localparam [0:0] RegFileWrenCheck = SecureIbex;
	localparam [31:0] RegFileDataWidth = (RegFileECC ? 39 : 32);
	localparam [0:0] MemECC = SecureIbex;
	localparam [31:0] MemDataWidth = (MemECC ? 39 : 32);
	localparam [31:0] ibex_pkg_BUS_SIZE = 32;
	localparam [31:0] BusSizeECC = (ICacheECC ? 39 : ibex_pkg_BUS_SIZE);
	localparam [31:0] ibex_pkg_BUS_BYTES = 4;
	localparam [31:0] ibex_pkg_IC_LINE_SIZE = 64;
	localparam [31:0] ibex_pkg_IC_LINE_BYTES = 8;
	localparam [31:0] ibex_pkg_IC_LINE_BEATS = ibex_pkg_IC_LINE_BYTES / ibex_pkg_BUS_BYTES;
	localparam [31:0] LineSizeECC = BusSizeECC * ibex_pkg_IC_LINE_BEATS;
	localparam [31:0] ibex_pkg_ADDR_W = 32;
	localparam [31:0] ibex_pkg_IC_NUM_WAYS = 2;
	localparam [31:0] ibex_pkg_IC_SIZE_BYTES = 4096;
	localparam [31:0] ibex_pkg_IC_NUM_LINES = (ibex_pkg_IC_SIZE_BYTES / ibex_pkg_IC_NUM_WAYS) / ibex_pkg_IC_LINE_BYTES;
	localparam [31:0] ibex_pkg_IC_INDEX_W = $clog2(ibex_pkg_IC_NUM_LINES);
	localparam [31:0] ibex_pkg_IC_LINE_W = 3;
	localparam [31:0] ibex_pkg_IC_TAG_SIZE = ((ibex_pkg_ADDR_W - ibex_pkg_IC_INDEX_W) - ibex_pkg_IC_LINE_W) + 1;
	localparam [31:0] TagSizeECC = (ICacheECC ? ibex_pkg_IC_TAG_SIZE + 6 : ibex_pkg_IC_TAG_SIZE);
	localparam [31:0] NumAddrScrRounds = (ICacheScramble ? 2 : 0);
	localparam [31:0] NumDiffRounds = NumAddrScrRounds;
	wire clk;
	wire [3:0] core_busy_d;
	reg [3:0] core_busy_q;
	wire clock_en;
	wire irq_pending;
	wire dummy_instr_id;
	wire dummy_instr_wb;
	wire [4:0] rf_raddr_a;
	wire [4:0] rf_raddr_b;
	wire [4:0] rf_waddr_wb;
	wire rf_we_wb;
	wire [RegFileDataWidth - 1:0] rf_wdata_wb_ecc;
	wire [RegFileDataWidth - 1:0] rf_rdata_a_ecc;
	wire [RegFileDataWidth - 1:0] rf_rdata_a_ecc_buf;
	wire [RegFileDataWidth - 1:0] rf_rdata_b_ecc;
	wire [RegFileDataWidth - 1:0] rf_rdata_b_ecc_buf;
	wire [MemDataWidth - 1:0] data_wdata_core;
	wire [MemDataWidth - 1:0] data_rdata_core;
	wire [MemDataWidth - 1:0] instr_rdata_core;
	wire [1:0] ic_tag_req;
	wire ic_tag_write;
	wire [ibex_pkg_IC_INDEX_W - 1:0] ic_tag_addr;
	wire [TagSizeECC - 1:0] ic_tag_wdata;
	wire [(ibex_pkg_IC_NUM_WAYS * TagSizeECC) - 1:0] ic_tag_rdata;
	wire [1:0] ic_data_req;
	wire ic_data_write;
	wire [ibex_pkg_IC_INDEX_W - 1:0] ic_data_addr;
	wire [LineSizeECC - 1:0] ic_data_wdata;
	wire [(ibex_pkg_IC_NUM_WAYS * LineSizeECC) - 1:0] ic_data_rdata;
	wire ic_scr_key_req;
	wire core_alert_major_internal;
	wire core_alert_major_bus;
	wire core_alert_minor;
	wire lockstep_alert_major_internal;
	wire lockstep_alert_major_bus;
	wire lockstep_alert_minor;
	reg [127:0] scramble_key_q;
	reg [63:0] scramble_nonce_q;
	wire scramble_key_valid_d;
	reg scramble_key_valid_q;
	wire scramble_req_d;
	reg scramble_req_q;
	wire [3:0] fetch_enable_buf;
	localparam [3:0] ibex_pkg_IbexMuBiOff = 4'b1010;
	generate
		if (SecureIbex) begin : g_clock_en_secure
			prim_flop #(
				.Width(4),
				.ResetValue(ibex_pkg_IbexMuBiOff)
			) u_prim_core_busy_flop(
				.clk_i(clk_i),
				.rst_ni(rst_ni),
				.d_i(core_busy_d),
				.q_o(core_busy_q)
			);
			assign clock_en = (((core_busy_q != ibex_pkg_IbexMuBiOff) | debug_req_i) | irq_pending) | irq_nm_i;
		end
		else begin : g_clock_en_non_secure
			always @(posedge clk_i)
				if (!rst_ni)
					core_busy_q <= ibex_pkg_IbexMuBiOff;
				else
					core_busy_q <= core_busy_d;
			assign clock_en = ((core_busy_q[0] | debug_req_i) | irq_pending) | irq_nm_i;
			wire unused_core_busy;
			assign unused_core_busy = ^core_busy_q[3:1];
		end
	endgenerate
	assign core_sleep_o = ~clock_en;
	assign clk = clk_i;
	prim_buf #(.Width(4)) u_fetch_enable_buf(
		.in_i(fetch_enable_i),
		.out_o(fetch_enable_buf)
	);
	prim_buf #(.Width(RegFileDataWidth)) u_rf_rdata_a_ecc_buf(
		.in_i(rf_rdata_a_ecc),
		.out_o(rf_rdata_a_ecc_buf)
	);
	prim_buf #(.Width(RegFileDataWidth)) u_rf_rdata_b_ecc_buf(
		.in_i(rf_rdata_b_ecc),
		.out_o(rf_rdata_b_ecc_buf)
	);
	assign data_rdata_core[31:0] = data_rdata_i;
	assign instr_rdata_core[31:0] = instr_rdata_i;
	generate
		if (MemECC) begin : gen_mem_rdata_ecc
			assign data_rdata_core[38:32] = data_rdata_intg_i;
			assign instr_rdata_core[38:32] = instr_rdata_intg_i;
		end
		else begin : gen_non_mem_rdata_ecc
			wire unused_intg;
			assign unused_intg = ^{instr_rdata_intg_i, data_rdata_intg_i};
		end
	endgenerate
	ibex_core #(
		.PMPEnable(PMPEnable),
		.PMPGranularity(PMPGranularity),
		.PMPNumRegions(PMPNumRegions),
		.MHPMCounterNum(MHPMCounterNum),
		.MHPMCounterWidth(MHPMCounterWidth),
		.RV32E(RV32E),
		.RV32M(RV32M),
		.RV32B(RV32B),
		.BranchTargetALU(BranchTargetALU),
		.ICache(ICache),
		.ICacheECC(ICacheECC),
		.BusSizeECC(BusSizeECC),
		.TagSizeECC(TagSizeECC),
		.LineSizeECC(LineSizeECC),
		.BranchPredictor(BranchPredictor),
		.DbgTriggerEn(DbgTriggerEn),
		.DbgHwBreakNum(DbgHwBreakNum),
		.WritebackStage(WritebackStage),
		.ResetAll(ResetAll),
		.RndCnstLfsrSeed(RndCnstLfsrSeed),
		.RndCnstLfsrPerm(RndCnstLfsrPerm),
		.SecureIbex(SecureIbex),
		.DummyInstructions(DummyInstructions),
		.RegFileECC(RegFileECC),
		.RegFileDataWidth(RegFileDataWidth),
		.MemECC(MemECC),
		.MemDataWidth(MemDataWidth),
		.DmHaltAddr(DmHaltAddr),
		.DmExceptionAddr(DmExceptionAddr)
	) u_ibex_core(
		.clk_i(clk),
		.rst_ni(rst_ni),
		.hart_id_i(hart_id_i),
		.boot_addr_i(boot_addr_i),
		.instr_req_o(instr_req_o),
		.instr_gnt_i(instr_gnt_i),
		.instr_rvalid_i(instr_rvalid_i),
		.instr_addr_o(instr_addr_o),
		.instr_rdata_i(instr_rdata_core),
		.instr_err_i(instr_err_i),
		.data_req_o(data_req_o),
		.data_gnt_i(data_gnt_i),
		.data_rvalid_i(data_rvalid_i),
		.data_we_o(data_we_o),
		.data_be_o(data_be_o),
		.data_addr_o(data_addr_o),
		.data_wdata_o(data_wdata_core),
		.data_rdata_i(data_rdata_core),
		.data_err_i(data_err_i),
		.dummy_instr_id_o(dummy_instr_id),
		.dummy_instr_wb_o(dummy_instr_wb),
		.rf_raddr_a_o(rf_raddr_a),
		.rf_raddr_b_o(rf_raddr_b),
		.rf_waddr_wb_o(rf_waddr_wb),
		.rf_we_wb_o(rf_we_wb),
		.rf_wdata_wb_ecc_o(rf_wdata_wb_ecc),
		.rf_rdata_a_ecc_i(rf_rdata_a_ecc_buf),
		.rf_rdata_b_ecc_i(rf_rdata_b_ecc_buf),
		.ic_tag_req_o(ic_tag_req),
		.ic_tag_write_o(ic_tag_write),
		.ic_tag_addr_o(ic_tag_addr),
		.ic_tag_wdata_o(ic_tag_wdata),
		.ic_tag_rdata_i(ic_tag_rdata),
		.ic_data_req_o(ic_data_req),
		.ic_data_write_o(ic_data_write),
		.ic_data_addr_o(ic_data_addr),
		.ic_data_wdata_o(ic_data_wdata),
		.ic_data_rdata_i(ic_data_rdata),
		.ic_scr_key_valid_i(scramble_key_valid_q),
		.ic_scr_key_req_o(ic_scr_key_req),
		.irq_software_i(irq_software_i),
		.irq_timer_i(irq_timer_i),
		.irq_external_i(irq_external_i),
		.irq_fast_i(irq_fast_i),
		.irq_nm_i(irq_nm_i),
		.irq_pending_o(irq_pending),
		.debug_req_i(debug_req_i),
		.crash_dump_o(crash_dump_o),
		.double_fault_seen_o(double_fault_seen_o),
		.fetch_enable_i(fetch_enable_buf),
		.alert_minor_o(core_alert_minor),
		.alert_major_internal_o(core_alert_major_internal),
		.alert_major_bus_o(core_alert_major_bus),
		.core_busy_o(core_busy_d)
	);
	wire rf_alert_major_internal;
	localparam [38:0] prim_secded_pkg_SecdedInv3932ZeroWord = 39'h2a00000000;
	function automatic [RegFileDataWidth - 1:0] sv2v_cast_E67BC;
		input reg [RegFileDataWidth - 1:0] inp;
		sv2v_cast_E67BC = inp;
	endfunction
	generate
		if (RegFile == 32'sd0) begin : gen_regfile_ff
			ibex_register_file_ff #(
				.RV32E(RV32E),
				.DataWidth(RegFileDataWidth),
				.DummyInstructions(DummyInstructions),
				.WrenCheck(RegFileWrenCheck),
				.WordZeroVal(sv2v_cast_E67BC(prim_secded_pkg_SecdedInv3932ZeroWord))
			) register_file_i(
				.clk_i(clk),
				.rst_ni(rst_ni),
				.test_en_i(test_en_i),
				.dummy_instr_id_i(dummy_instr_id),
				.dummy_instr_wb_i(dummy_instr_wb),
				.raddr_a_i(rf_raddr_a),
				.rdata_a_o(rf_rdata_a_ecc),
				.raddr_b_i(rf_raddr_b),
				.rdata_b_o(rf_rdata_b_ecc),
				.waddr_a_i(rf_waddr_wb),
				.wdata_a_i(rf_wdata_wb_ecc),
				.we_a_i(rf_we_wb),
				.err_o(rf_alert_major_internal)
			);
		end
		else if (RegFile == 32'sd1) begin : gen_regfile_fpga
			ibex_register_file_fpga #(
				.RV32E(RV32E),
				.DataWidth(RegFileDataWidth),
				.DummyInstructions(DummyInstructions),
				.WrenCheck(RegFileWrenCheck),
				.WordZeroVal(sv2v_cast_E67BC(prim_secded_pkg_SecdedInv3932ZeroWord))
			) register_file_i(
				.clk_i(clk),
				.rst_ni(rst_ni),
				.test_en_i(test_en_i),
				.dummy_instr_id_i(dummy_instr_id),
				.dummy_instr_wb_i(dummy_instr_wb),
				.raddr_a_i(rf_raddr_a),
				.rdata_a_o(rf_rdata_a_ecc),
				.raddr_b_i(rf_raddr_b),
				.rdata_b_o(rf_rdata_b_ecc),
				.waddr_a_i(rf_waddr_wb),
				.wdata_a_i(rf_wdata_wb_ecc),
				.we_a_i(rf_we_wb),
				.err_o(rf_alert_major_internal)
			);
		end
		else if (RegFile == 32'sd2) begin : gen_regfile_latch
			ibex_register_file_latch #(
				.RV32E(RV32E),
				.DataWidth(RegFileDataWidth),
				.DummyInstructions(DummyInstructions),
				.WrenCheck(RegFileWrenCheck),
				.WordZeroVal(sv2v_cast_E67BC(prim_secded_pkg_SecdedInv3932ZeroWord))
			) register_file_i(
				.clk_i(clk),
				.rst_ni(rst_ni),
				.test_en_i(test_en_i),
				.dummy_instr_id_i(dummy_instr_id),
				.dummy_instr_wb_i(dummy_instr_wb),
				.raddr_a_i(rf_raddr_a),
				.rdata_a_o(rf_rdata_a_ecc),
				.raddr_b_i(rf_raddr_b),
				.rdata_b_o(rf_rdata_b_ecc),
				.waddr_a_i(rf_waddr_wb),
				.wdata_a_i(rf_wdata_wb_ecc),
				.we_a_i(rf_we_wb),
				.err_o(rf_alert_major_internal)
			);
		end
		if (ICacheScramble) begin : gen_scramble
			assign scramble_key_valid_d = (scramble_req_q ? scramble_key_valid_i : (ic_scr_key_req ? 1'b0 : scramble_key_valid_q));
			always @(posedge clk_i)
				if (!rst_ni) begin
					scramble_key_q <= RndCnstIbexKey;
					scramble_nonce_q <= RndCnstIbexNonce;
				end
				else if (scramble_key_valid_i) begin
					scramble_key_q <= scramble_key_i;
					scramble_nonce_q <= scramble_nonce_i;
				end
			always @(posedge clk_i)
				if (!rst_ni) begin
					scramble_key_valid_q <= 1'b1;
					scramble_req_q <= 1'sb0;
				end
				else begin
					scramble_key_valid_q <= scramble_key_valid_d;
					scramble_req_q <= scramble_req_d;
				end
			assign scramble_req_d = (scramble_req_q ? ~scramble_key_valid_i : ic_scr_key_req);
			assign scramble_req_o = scramble_req_q;
		end
		else begin : gen_noscramble
			reg unused_scramble_inputs = (((((((scramble_key_valid_i & |scramble_key_i) & |RndCnstIbexKey) & |scramble_nonce_i) & |RndCnstIbexNonce) & scramble_req_q) & ic_scr_key_req) & scramble_key_valid_d) & scramble_req_d;
			assign scramble_req_d = 1'b0;
			wire [1:1] sv2v_tmp_AE3A4;
			assign sv2v_tmp_AE3A4 = 1'b0;
			always @(*) scramble_req_q = sv2v_tmp_AE3A4;
			assign scramble_req_o = 1'b0;
			wire [128:1] sv2v_tmp_A2325;
			assign sv2v_tmp_A2325 = 1'sb0;
			always @(*) scramble_key_q = sv2v_tmp_A2325;
			wire [64:1] sv2v_tmp_70913;
			assign sv2v_tmp_70913 = 1'sb0;
			always @(*) scramble_nonce_q = sv2v_tmp_70913;
			wire [1:1] sv2v_tmp_92821;
			assign sv2v_tmp_92821 = 1'b1;
			always @(*) scramble_key_valid_q = sv2v_tmp_92821;
			assign scramble_key_valid_d = 1'b1;
		end
	endgenerate
	function automatic [TagSizeECC - 1:0] sv2v_cast_BD0FC;
		input reg [TagSizeECC - 1:0] inp;
		sv2v_cast_BD0FC = inp;
	endfunction
	function automatic [LineSizeECC - 1:0] sv2v_cast_F09E7;
		input reg [LineSizeECC - 1:0] inp;
		sv2v_cast_F09E7 = inp;
	endfunction
	generate
		if (ICache) begin : gen_rams
			genvar way;
			for (way = 0; way < ibex_pkg_IC_NUM_WAYS; way = way + 1) begin : gen_rams_inner
				if (ICacheScramble) begin : gen_scramble_rams
					prim_ram_1p_scr #(
						.Width(TagSizeECC),
						.Depth(ibex_pkg_IC_NUM_LINES),
						.DataBitsPerMask(TagSizeECC),
						.EnableParity(0),
						.DiffWidth(TagSizeECC),
						.NumAddrScrRounds(NumAddrScrRounds),
						.NumDiffRounds(NumDiffRounds)
					) tag_bank(
						.clk_i(clk_i),
						.rst_ni(rst_ni),
						.key_valid_i(scramble_key_valid_q),
						.key_i(scramble_key_q),
						.nonce_i(scramble_nonce_q),
						.req_i(ic_tag_req[way]),
						.gnt_o(),
						.write_i(ic_tag_write),
						.addr_i(ic_tag_addr),
						.wdata_i(ic_tag_wdata),
						.wmask_i({TagSizeECC {1'b1}}),
						.intg_error_i(1'b0),
						.rdata_o(ic_tag_rdata[(1 - way) * TagSizeECC+:TagSizeECC]),
						.rvalid_o(),
						.raddr_o(),
						.rerror_o(),
						.cfg_i(ram_cfg_i)
					);
					prim_ram_1p_scr #(
						.Width(LineSizeECC),
						.Depth(ibex_pkg_IC_NUM_LINES),
						.DataBitsPerMask(LineSizeECC),
						.ReplicateKeyStream(1),
						.EnableParity(0),
						.DiffWidth(LineSizeECC),
						.NumAddrScrRounds(NumAddrScrRounds),
						.NumDiffRounds(NumDiffRounds)
					) data_bank(
						.clk_i(clk_i),
						.rst_ni(rst_ni),
						.key_valid_i(scramble_key_valid_q),
						.key_i(scramble_key_q),
						.nonce_i(scramble_nonce_q),
						.req_i(ic_data_req[way]),
						.gnt_o(),
						.write_i(ic_data_write),
						.addr_i(ic_data_addr),
						.wdata_i(ic_data_wdata),
						.wmask_i({LineSizeECC {1'b1}}),
						.intg_error_i(1'b0),
						.rdata_o(ic_data_rdata[(1 - way) * LineSizeECC+:LineSizeECC]),
						.rvalid_o(),
						.raddr_o(),
						.rerror_o(),
						.cfg_i(ram_cfg_i)
					);
				end
				else begin : gen_noscramble_rams
					prim_ram_1p #(
						.Width(TagSizeECC),
						.Depth(ibex_pkg_IC_NUM_LINES),
						.DataBitsPerMask(TagSizeECC)
					) tag_bank(
						.clk_i(clk_i),
						.req_i(ic_tag_req[way]),
						.write_i(ic_tag_write),
						.addr_i(ic_tag_addr),
						.wdata_i(ic_tag_wdata),
						.wmask_i({TagSizeECC {1'b1}}),
						.rdata_o(ic_tag_rdata[(1 - way) * TagSizeECC+:TagSizeECC]),
						.cfg_i(ram_cfg_i)
					);
					prim_ram_1p #(
						.Width(LineSizeECC),
						.Depth(ibex_pkg_IC_NUM_LINES),
						.DataBitsPerMask(LineSizeECC)
					) data_bank(
						.clk_i(clk_i),
						.req_i(ic_data_req[way]),
						.write_i(ic_data_write),
						.addr_i(ic_data_addr),
						.wdata_i(ic_data_wdata),
						.wmask_i({LineSizeECC {1'b1}}),
						.rdata_o(ic_data_rdata[(1 - way) * LineSizeECC+:LineSizeECC]),
						.cfg_i(ram_cfg_i)
					);
				end
			end
		end
		else begin : gen_norams
			wire [9:0] unused_ram_cfg;
			wire unused_ram_inputs;
			assign unused_ram_cfg = ram_cfg_i;
			assign unused_ram_inputs = ((((((((((((|ic_tag_req & ic_tag_write) & |ic_tag_addr) & |ic_tag_wdata) & |ic_data_req) & ic_data_write) & |ic_data_addr) & |ic_data_wdata) & |scramble_key_q) & |scramble_nonce_q) & scramble_key_valid_q) & scramble_key_valid_d) & |scramble_nonce_q) & |NumAddrScrRounds;
			assign ic_tag_rdata = {ibex_pkg_IC_NUM_WAYS {sv2v_cast_BD0FC('b0)}};
			assign ic_data_rdata = {ibex_pkg_IC_NUM_WAYS {sv2v_cast_F09E7('b0)}};
		end
	endgenerate
	assign data_wdata_o = data_wdata_core[31:0];
	generate
		if (MemECC) begin : gen_mem_wdata_ecc
			prim_buf #(.Width(7)) u_prim_buf_data_wdata_intg(
				.in_i(data_wdata_core[38:32]),
				.out_o(data_wdata_intg_o)
			);
		end
		else begin : gen_no_mem_ecc
			assign data_wdata_intg_o = 1'sb0;
		end
		if (Lockstep) begin : gen_lockstep
			localparam signed [31:0] NumBufferBits = ((((((((((((((((99 + MemDataWidth) + 41) + MemDataWidth) + MemDataWidth) + 19) + RegFileDataWidth) + RegFileDataWidth) + RegFileDataWidth) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + TagSizeECC) + ibex_pkg_IC_NUM_WAYS) + 1) + ibex_pkg_IC_INDEX_W) + LineSizeECC) + 192;
			wire [NumBufferBits - 1:0] buf_in;
			wire [NumBufferBits - 1:0] buf_out;
			wire [31:0] hart_id_local;
			wire [31:0] boot_addr_local;
			wire instr_req_local;
			wire instr_gnt_local;
			wire instr_rvalid_local;
			wire [31:0] instr_addr_local;
			wire [MemDataWidth - 1:0] instr_rdata_local;
			wire instr_err_local;
			wire data_req_local;
			wire data_gnt_local;
			wire data_rvalid_local;
			wire data_we_local;
			wire [3:0] data_be_local;
			wire [31:0] data_addr_local;
			wire [MemDataWidth - 1:0] data_wdata_local;
			wire [MemDataWidth - 1:0] data_rdata_local;
			wire data_err_local;
			wire dummy_instr_id_local;
			wire dummy_instr_wb_local;
			wire [4:0] rf_raddr_a_local;
			wire [4:0] rf_raddr_b_local;
			wire [4:0] rf_waddr_wb_local;
			wire rf_we_wb_local;
			wire [RegFileDataWidth - 1:0] rf_wdata_wb_ecc_local;
			wire [RegFileDataWidth - 1:0] rf_rdata_a_ecc_local;
			wire [RegFileDataWidth - 1:0] rf_rdata_b_ecc_local;
			wire [1:0] ic_tag_req_local;
			wire ic_tag_write_local;
			wire [ibex_pkg_IC_INDEX_W - 1:0] ic_tag_addr_local;
			wire [TagSizeECC - 1:0] ic_tag_wdata_local;
			wire [1:0] ic_data_req_local;
			wire ic_data_write_local;
			wire [ibex_pkg_IC_INDEX_W - 1:0] ic_data_addr_local;
			wire [LineSizeECC - 1:0] ic_data_wdata_local;
			wire scramble_key_valid_local;
			wire ic_scr_key_req_local;
			wire irq_software_local;
			wire irq_timer_local;
			wire irq_external_local;
			wire [14:0] irq_fast_local;
			wire irq_nm_local;
			wire irq_pending_local;
			wire debug_req_local;
			wire [159:0] crash_dump_local;
			wire double_fault_seen_local;
			wire [3:0] fetch_enable_local;
			wire [3:0] core_busy_local;
			assign buf_in = {hart_id_i, boot_addr_i, instr_req_o, instr_gnt_i, instr_rvalid_i, instr_addr_o, instr_rdata_core, instr_err_i, data_req_o, data_gnt_i, data_rvalid_i, data_we_o, data_be_o, data_addr_o, data_wdata_core, data_rdata_core, data_err_i, dummy_instr_id, dummy_instr_wb, rf_raddr_a, rf_raddr_b, rf_waddr_wb, rf_we_wb, rf_wdata_wb_ecc, rf_rdata_a_ecc, rf_rdata_b_ecc, ic_tag_req, ic_tag_write, ic_tag_addr, ic_tag_wdata, ic_data_req, ic_data_write, ic_data_addr, ic_data_wdata, scramble_key_valid_q, ic_scr_key_req, irq_software_i, irq_timer_i, irq_external_i, irq_fast_i, irq_nm_i, irq_pending, debug_req_i, crash_dump_o, double_fault_seen_o, fetch_enable_i, core_busy_d};
			assign {hart_id_local, boot_addr_local, instr_req_local, instr_gnt_local, instr_rvalid_local, instr_addr_local, instr_rdata_local, instr_err_local, data_req_local, data_gnt_local, data_rvalid_local, data_we_local, data_be_local, data_addr_local, data_wdata_local, data_rdata_local, data_err_local, dummy_instr_id_local, dummy_instr_wb_local, rf_raddr_a_local, rf_raddr_b_local, rf_waddr_wb_local, rf_we_wb_local, rf_wdata_wb_ecc_local, rf_rdata_a_ecc_local, rf_rdata_b_ecc_local, ic_tag_req_local, ic_tag_write_local, ic_tag_addr_local, ic_tag_wdata_local, ic_data_req_local, ic_data_write_local, ic_data_addr_local, ic_data_wdata_local, scramble_key_valid_local, ic_scr_key_req_local, irq_software_local, irq_timer_local, irq_external_local, irq_fast_local, irq_nm_local, irq_pending_local, debug_req_local, crash_dump_local, double_fault_seen_local, fetch_enable_local, core_busy_local} = buf_out;
			prim_buf #(.Width(NumBufferBits)) u_signals_prim_buf(
				.in_i(buf_in),
				.out_o(buf_out)
			);
			wire [(ibex_pkg_IC_NUM_WAYS * TagSizeECC) - 1:0] ic_tag_rdata_local;
			wire [(ibex_pkg_IC_NUM_WAYS * LineSizeECC) - 1:0] ic_data_rdata_local;
			genvar k;
			for (k = 0; k < ibex_pkg_IC_NUM_WAYS; k = k + 1) begin : gen_ways
				prim_buf #(.Width(TagSizeECC)) u_tag_prim_buf(
					.in_i(ic_tag_rdata[(1 - k) * TagSizeECC+:TagSizeECC]),
					.out_o(ic_tag_rdata_local[(1 - k) * TagSizeECC+:TagSizeECC])
				);
				prim_buf #(.Width(LineSizeECC)) u_data_prim_buf(
					.in_i(ic_data_rdata[(1 - k) * LineSizeECC+:LineSizeECC]),
					.out_o(ic_data_rdata_local[(1 - k) * LineSizeECC+:LineSizeECC])
				);
			end
			wire lockstep_alert_minor_local;
			wire lockstep_alert_major_internal_local;
			wire lockstep_alert_major_bus_local;
			ibex_lockstep #(
				.PMPEnable(PMPEnable),
				.PMPGranularity(PMPGranularity),
				.PMPNumRegions(PMPNumRegions),
				.MHPMCounterNum(MHPMCounterNum),
				.MHPMCounterWidth(MHPMCounterWidth),
				.RV32E(RV32E),
				.RV32M(RV32M),
				.RV32B(RV32B),
				.BranchTargetALU(BranchTargetALU),
				.ICache(ICache),
				.ICacheECC(ICacheECC),
				.BusSizeECC(BusSizeECC),
				.TagSizeECC(TagSizeECC),
				.LineSizeECC(LineSizeECC),
				.BranchPredictor(BranchPredictor),
				.DbgTriggerEn(DbgTriggerEn),
				.DbgHwBreakNum(DbgHwBreakNum),
				.WritebackStage(WritebackStage),
				.ResetAll(ResetAll),
				.RndCnstLfsrSeed(RndCnstLfsrSeed),
				.RndCnstLfsrPerm(RndCnstLfsrPerm),
				.SecureIbex(SecureIbex),
				.DummyInstructions(DummyInstructions),
				.RegFileECC(RegFileECC),
				.RegFileDataWidth(RegFileDataWidth),
				.MemECC(MemECC),
				.DmHaltAddr(DmHaltAddr),
				.DmExceptionAddr(DmExceptionAddr)
			) u_ibex_lockstep(
				.clk_i(clk),
				.rst_ni(rst_ni),
				.hart_id_i(hart_id_local),
				.boot_addr_i(boot_addr_local),
				.instr_req_i(instr_req_local),
				.instr_gnt_i(instr_gnt_local),
				.instr_rvalid_i(instr_rvalid_local),
				.instr_addr_i(instr_addr_local),
				.instr_rdata_i(instr_rdata_local),
				.instr_err_i(instr_err_local),
				.data_req_i(data_req_local),
				.data_gnt_i(data_gnt_local),
				.data_rvalid_i(data_rvalid_local),
				.data_we_i(data_we_local),
				.data_be_i(data_be_local),
				.data_addr_i(data_addr_local),
				.data_wdata_i(data_wdata_local),
				.data_rdata_i(data_rdata_local),
				.data_err_i(data_err_local),
				.dummy_instr_id_i(dummy_instr_id_local),
				.dummy_instr_wb_i(dummy_instr_wb_local),
				.rf_raddr_a_i(rf_raddr_a_local),
				.rf_raddr_b_i(rf_raddr_b_local),
				.rf_waddr_wb_i(rf_waddr_wb_local),
				.rf_we_wb_i(rf_we_wb_local),
				.rf_wdata_wb_ecc_i(rf_wdata_wb_ecc_local),
				.rf_rdata_a_ecc_i(rf_rdata_a_ecc_local),
				.rf_rdata_b_ecc_i(rf_rdata_b_ecc_local),
				.ic_tag_req_i(ic_tag_req_local),
				.ic_tag_write_i(ic_tag_write_local),
				.ic_tag_addr_i(ic_tag_addr_local),
				.ic_tag_wdata_i(ic_tag_wdata_local),
				.ic_tag_rdata_i(ic_tag_rdata_local),
				.ic_data_req_i(ic_data_req_local),
				.ic_data_write_i(ic_data_write_local),
				.ic_data_addr_i(ic_data_addr_local),
				.ic_data_wdata_i(ic_data_wdata_local),
				.ic_data_rdata_i(ic_data_rdata_local),
				.ic_scr_key_valid_i(scramble_key_valid_local),
				.ic_scr_key_req_i(ic_scr_key_req_local),
				.irq_software_i(irq_software_local),
				.irq_timer_i(irq_timer_local),
				.irq_external_i(irq_external_local),
				.irq_fast_i(irq_fast_local),
				.irq_nm_i(irq_nm_local),
				.irq_pending_i(irq_pending_local),
				.debug_req_i(debug_req_local),
				.crash_dump_i(crash_dump_local),
				.double_fault_seen_i(double_fault_seen_local),
				.fetch_enable_i(fetch_enable_local),
				.alert_minor_o(lockstep_alert_minor_local),
				.alert_major_internal_o(lockstep_alert_major_internal_local),
				.alert_major_bus_o(lockstep_alert_major_bus_local),
				.core_busy_i(core_busy_local),
				.test_en_i(test_en_i),
				.scan_rst_ni(scan_rst_ni)
			);
			prim_buf u_prim_buf_alert_minor(
				.in_i(lockstep_alert_minor_local),
				.out_o(lockstep_alert_minor)
			);
			prim_buf u_prim_buf_alert_major_internal(
				.in_i(lockstep_alert_major_internal_local),
				.out_o(lockstep_alert_major_internal)
			);
			prim_buf u_prim_buf_alert_major_bus(
				.in_i(lockstep_alert_major_bus_local),
				.out_o(lockstep_alert_major_bus)
			);
		end
		else begin : gen_no_lockstep
			assign lockstep_alert_major_internal = 1'b0;
			assign lockstep_alert_major_bus = 1'b0;
			assign lockstep_alert_minor = 1'b0;
			wire unused_scan;
			assign unused_scan = scan_rst_ni;
		end
	endgenerate
	assign alert_major_internal_o = (core_alert_major_internal | lockstep_alert_major_internal) | rf_alert_major_internal;
	assign alert_major_bus_o = core_alert_major_bus | lockstep_alert_major_bus;
	assign alert_minor_o = core_alert_minor | lockstep_alert_minor;
endmodule
module pwr (
	clk,
	resetn,
	mem_valid,
	mem_addr,
	mem_wdata,
	mem_wstrb,
	pwr_ready,
	pwr_sel,
	poweroff_rq
);
	parameter [31:0] ADDR = 32'hffffffff;
	input clk;
	input resetn;
	input mem_valid;
	input [31:0] mem_addr;
	input [31:0] mem_wdata;
	input [3:0] mem_wstrb;
	output wire pwr_ready;
	output wire pwr_sel;
	output reg poweroff_rq;
	assign pwr_sel = mem_valid && (mem_addr == ADDR);
	assign pwr_ready = 1;
	always @(posedge clk)
		if (!resetn)
			poweroff_rq <= 0;
		else if (pwr_sel && mem_wstrb[0])
			poweroff_rq <= mem_wdata[7:0] != 0;
endmodule
module rom (
	clk,
	valid1,
	addr1,
	dout1,
	ready1,
	valid2,
	addr2,
	dout2,
	ready2
);
	parameter ADDR_BITS = 10;
	parameter FILENAME = "rom.mem";
	input clk;
	input valid1;
	input [31:0] addr1;
	output wire [31:0] dout1;
	output wire ready1;
	input valid2;
	input [31:0] addr2;
	output wire [31:0] dout2;
	output wire ready2;
	reg [31:0] rom [(2 ** (ADDR_BITS - 2)) - 1:0];
	initial $readmemh(FILENAME, rom);
	wire [ADDR_BITS - 3:0] xaddr;
	assign xaddr = 0;
	always @(posedge clk) rom[xaddr] <= rom[xaddr];
	wire [ADDR_BITS - 3:0] idx1 = addr1[ADDR_BITS - 1:2];
	assign dout1 = rom[idx1];
	assign ready1 = valid1;
	wire [ADDR_BITS - 3:0] idx2 = addr2[ADDR_BITS - 1:2];
	assign dout2 = rom[idx2];
	assign ready2 = valid2;
endmodule
module soc (
	clk,
	resetn,
	poweroff_rq,
	uart_tx,
	uart_rx,
	uart_cts,
	uart_rts
);
	parameter FIRMWARE_FILE = "firmware.mem";
	parameter ROM_ADDR_BITS = 12;
	parameter RAM_ADDR_BITS = 17;
	parameter FRAM_ADDR_BITS = 20;
	input clk;
	input resetn;
	output wire poweroff_rq;
	output wire uart_tx;
	input uart_rx;
	input uart_cts;
	output wire uart_rts;
	wire mem_valid;
	wire mem_instr;
	wire mem_ready;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0] mem_wstrb;
	wire data_we_o;
	wire [3:0] data_be_o;
	wire [31:0] mem_rdata;
	assign mem_wstrb = (!data_we_o ? 4'b0000 : data_be_o);
	wire instr_req_o;
	wire [31:0] instr_addr_o;
	wire instr_rvalid_i;
	wire [31:0] instr_rdata_i;
	reg [31:0] instr_rdata_reg;
	reg instr_rvalid_reg;
	reg [31:0] mem_rdata_reg;
	reg mem_ready_reg;
	ibex_top #(
		.PMPEnable(1),
		.ResetAllOnStart(1)
	) cpu(
		.clk_i(clk),
		.rst_ni(resetn),
		.test_en_i(0),
		.scan_rst_ni(1),
		.ram_cfg_i(0),
		.hart_id_i(32'h00000000),
		.boot_addr_i(32'h00000000),
		.instr_req_o(instr_req_o),
		.instr_gnt_i(instr_rvalid_i),
		.instr_rvalid_i(instr_rvalid_reg),
		.instr_addr_o(instr_addr_o),
		.instr_rdata_i(instr_rdata_reg),
		.instr_err_i(0),
		.data_req_o(mem_valid),
		.data_gnt_i(mem_ready),
		.data_rvalid_i(mem_ready_reg),
		.data_we_o(data_we_o),
		.data_be_o(data_be_o),
		.data_addr_o(mem_addr),
		.data_wdata_o(mem_wdata),
		.data_rdata_i(mem_rdata_reg),
		.data_err_i(0),
		.irq_software_i(0),
		.irq_timer_i(0),
		.irq_external_i(0),
		.irq_fast_i(0),
		.irq_nm_i(0),
		.debug_req_i(0),
		.fetch_enable_i(4'b0101)
	);
	always @(posedge clk)
		if (!resetn) begin
			instr_rdata_reg <= 32'h00000000;
			instr_rvalid_reg <= 0;
			mem_rdata_reg <= 32'h00000000;
			mem_ready_reg <= 0;
		end
		else begin
			instr_rdata_reg <= instr_rdata_i;
			instr_rvalid_reg <= instr_rvalid_i;
			mem_rdata_reg <= mem_rdata;
			mem_ready_reg <= mem_ready;
		end
	wire instr_valid = instr_req_o && (instr_addr_o[31:24] == 8'h00);
	wire [31:0] instr_rdata;
	wire instr_ready;
	wire rom_valid = mem_valid && (mem_addr[31:24] == 8'h00);
	wire [31:0] rom_rdata;
	wire rom_ready;
	rom #(
		.ADDR_BITS(ROM_ADDR_BITS),
		.FILENAME(FIRMWARE_FILE)
	) rom(
		.clk(clk),
		.valid1(instr_valid),
		.addr1(instr_addr_o),
		.dout1(instr_rdata),
		.ready1(instr_ready),
		.valid2(rom_valid),
		.addr2(mem_addr),
		.dout2(rom_rdata),
		.ready2(rom_ready)
	);
	assign instr_rvalid_i = instr_valid && instr_ready;
	assign instr_rdata_i = (instr_valid && instr_ready ? instr_rdata : 32'h00000000);
	wire fram_valid;
	wire fram_ready;
	wire [31:0] fram_rdata;
	assign fram_valid = mem_valid && (mem_addr[31:24] == 8'h10);
	fram #(.ADDR_BITS(FRAM_ADDR_BITS)) fram(
		.clk(clk),
		.resetn(resetn),
		.valid(fram_valid),
		.addr(mem_addr),
		.din(mem_wdata),
		.wstrb(mem_wstrb),
		.dout(fram_rdata),
		.ready(fram_ready)
	);
	wire ram_valid = mem_valid && (mem_addr[31:24] == 8'h20);
	wire [31:0] ram_rdata;
	wire ram_ready;
	ram #(.ADDR_BITS(RAM_ADDR_BITS)) ram(
		.clk(clk),
		.resetn(resetn),
		.valid(ram_valid),
		.addr(mem_addr),
		.din(mem_wdata),
		.wstrb(mem_wstrb),
		.dout(ram_rdata),
		.ready(ram_ready)
	);
	wire pwr_ready;
	wire pwr_sel;
	pwr #(.ADDR(32'h40000000)) pwr(
		.clk(clk),
		.resetn(resetn),
		.mem_valid(mem_valid),
		.mem_addr(mem_addr),
		.mem_wdata(mem_wdata),
		.mem_wstrb(mem_wstrb),
		.pwr_ready(pwr_ready),
		.pwr_sel(pwr_sel),
		.poweroff_rq(poweroff_rq)
	);
	wire uart_ready;
	wire uart_sel;
	wire [31:0] uart_rdata;
	uart #(.ADDR(32'h40001000)) uart(
		.clk(clk),
		.resetn(resetn),
		.ser_tx(uart_tx),
		.ser_rx(uart_rx),
		.ser_cts(uart_cts),
		.ser_rts(uart_rts),
		.mem_valid(mem_valid),
		.mem_addr(mem_addr),
		.mem_wdata(mem_wdata),
		.mem_wstrb(mem_wstrb),
		.uart_ready(uart_ready),
		.uart_sel(uart_sel),
		.uart_rdata(uart_rdata)
	);
	assign mem_ready = ((((rom_valid && rom_ready) || (fram_valid && fram_ready)) || (ram_valid && ram_ready)) || (pwr_sel && pwr_ready)) || (uart_sel && uart_ready);
	assign mem_rdata = (rom_valid && rom_ready ? rom_rdata : (fram_valid && fram_ready ? fram_rdata : (ram_valid && ram_ready ? ram_rdata : (uart_sel ? uart_rdata : 32'h00000000))));
endmodule
module picorv32 (
	clk,
	resetn,
	trap,
	mem_valid,
	mem_instr,
	mem_ready,
	mem_addr,
	mem_wdata,
	mem_wstrb,
	mem_rdata,
	mem_la_read,
	mem_la_write,
	mem_la_addr,
	mem_la_wdata,
	mem_la_wstrb,
	pcpi_valid,
	pcpi_insn,
	pcpi_rs1,
	pcpi_rs2,
	pcpi_wr,
	pcpi_rd,
	pcpi_wait,
	pcpi_ready,
	irq,
	eoi,
	trace_valid,
	trace_data
);
	parameter [0:0] ENABLE_COUNTERS = 1;
	parameter [0:0] ENABLE_COUNTERS64 = 1;
	parameter [0:0] ENABLE_REGS_16_31 = 1;
	parameter [0:0] ENABLE_REGS_DUALPORT = 1;
	parameter [0:0] LATCHED_MEM_RDATA = 0;
	parameter [0:0] TWO_STAGE_SHIFT = 1;
	parameter [0:0] BARREL_SHIFTER = 0;
	parameter [0:0] TWO_CYCLE_COMPARE = 0;
	parameter [0:0] TWO_CYCLE_ALU = 0;
	parameter [0:0] COMPRESSED_ISA = 0;
	parameter [0:0] CATCH_MISALIGN = 1;
	parameter [0:0] CATCH_ILLINSN = 1;
	parameter [0:0] ENABLE_PCPI = 0;
	parameter [0:0] ENABLE_MUL = 0;
	parameter [0:0] ENABLE_FAST_MUL = 0;
	parameter [0:0] ENABLE_DIV = 0;
	parameter [0:0] ENABLE_IRQ = 0;
	parameter [0:0] ENABLE_IRQ_QREGS = 1;
	parameter [0:0] ENABLE_IRQ_TIMER = 1;
	parameter [0:0] ENABLE_TRACE = 0;
	parameter [0:0] REGS_INIT_ZERO = 0;
	parameter [31:0] MASKED_IRQ = 32'h00000000;
	parameter [31:0] LATCHED_IRQ = 32'hffffffff;
	parameter [31:0] PROGADDR_RESET = 32'h00000000;
	parameter [31:0] PROGADDR_IRQ = 32'h00000010;
	parameter [31:0] STACKADDR = 32'hffffffff;
	input clk;
	input resetn;
	output reg trap;
	output reg mem_valid;
	output reg mem_instr;
	input mem_ready;
	output reg [31:0] mem_addr;
	output reg [31:0] mem_wdata;
	output reg [3:0] mem_wstrb;
	input [31:0] mem_rdata;
	output wire mem_la_read;
	output wire mem_la_write;
	output wire [31:0] mem_la_addr;
	output reg [31:0] mem_la_wdata;
	output reg [3:0] mem_la_wstrb;
	output reg pcpi_valid;
	output reg [31:0] pcpi_insn;
	output wire [31:0] pcpi_rs1;
	output wire [31:0] pcpi_rs2;
	input pcpi_wr;
	input [31:0] pcpi_rd;
	input pcpi_wait;
	input pcpi_ready;
	input [31:0] irq;
	output reg [31:0] eoi;
	output reg trace_valid;
	output reg [35:0] trace_data;
	localparam integer irq_timer = 0;
	localparam integer irq_ebreak = 1;
	localparam integer irq_buserror = 2;
	localparam integer irqregs_offset = (ENABLE_REGS_16_31 ? 32 : 16);
	localparam integer regfile_size = (ENABLE_REGS_16_31 ? 32 : 16) + ((4 * ENABLE_IRQ) * ENABLE_IRQ_QREGS);
	localparam integer regindex_bits = (ENABLE_REGS_16_31 ? 5 : 4) + (ENABLE_IRQ * ENABLE_IRQ_QREGS);
	localparam WITH_PCPI = ((ENABLE_PCPI || ENABLE_MUL) || ENABLE_FAST_MUL) || ENABLE_DIV;
	localparam [35:0] TRACE_BRANCH = 36'b000100000000000000000000000000000000;
	localparam [35:0] TRACE_ADDR = 36'b001000000000000000000000000000000000;
	localparam [35:0] TRACE_IRQ = 36'b100000000000000000000000000000000000;
	reg [63:0] count_cycle;
	reg [63:0] count_instr;
	reg [31:0] reg_pc;
	reg [31:0] reg_next_pc;
	reg [31:0] reg_op1;
	reg [31:0] reg_op2;
	reg [31:0] reg_out;
	reg [4:0] reg_sh;
	reg [31:0] next_insn_opcode;
	reg [31:0] dbg_insn_opcode;
	reg [31:0] dbg_insn_addr;
	wire dbg_mem_valid = mem_valid;
	wire dbg_mem_instr = mem_instr;
	wire dbg_mem_ready = mem_ready;
	wire [31:0] dbg_mem_addr = mem_addr;
	wire [31:0] dbg_mem_wdata = mem_wdata;
	wire [3:0] dbg_mem_wstrb = mem_wstrb;
	wire [31:0] dbg_mem_rdata = mem_rdata;
	assign pcpi_rs1 = reg_op1;
	assign pcpi_rs2 = reg_op2;
	wire [31:0] next_pc;
	reg irq_delay;
	reg irq_active;
	reg [31:0] irq_mask;
	reg [31:0] irq_pending;
	reg [31:0] timer;
	reg [31:0] cpuregs [0:regfile_size - 1];
	integer i;
	initial if (REGS_INIT_ZERO)
		for (i = 0; i < regfile_size; i = i + 1)
			cpuregs[i] = 0;
	task empty_statement;
		;
	endtask
	wire pcpi_mul_wr;
	wire [31:0] pcpi_mul_rd;
	wire pcpi_mul_wait;
	wire pcpi_mul_ready;
	wire pcpi_div_wr;
	wire [31:0] pcpi_div_rd;
	wire pcpi_div_wait;
	wire pcpi_div_ready;
	reg pcpi_int_wr;
	reg [31:0] pcpi_int_rd;
	reg pcpi_int_wait;
	reg pcpi_int_ready;
	generate
		if (ENABLE_FAST_MUL) begin : genblk1
			picorv32_pcpi_fast_mul pcpi_mul(
				.clk(clk),
				.resetn(resetn),
				.pcpi_valid(pcpi_valid),
				.pcpi_insn(pcpi_insn),
				.pcpi_rs1(pcpi_rs1),
				.pcpi_rs2(pcpi_rs2),
				.pcpi_wr(pcpi_mul_wr),
				.pcpi_rd(pcpi_mul_rd),
				.pcpi_wait(pcpi_mul_wait),
				.pcpi_ready(pcpi_mul_ready)
			);
		end
		else if (ENABLE_MUL) begin : genblk1
			picorv32_pcpi_mul pcpi_mul(
				.clk(clk),
				.resetn(resetn),
				.pcpi_valid(pcpi_valid),
				.pcpi_insn(pcpi_insn),
				.pcpi_rs1(pcpi_rs1),
				.pcpi_rs2(pcpi_rs2),
				.pcpi_wr(pcpi_mul_wr),
				.pcpi_rd(pcpi_mul_rd),
				.pcpi_wait(pcpi_mul_wait),
				.pcpi_ready(pcpi_mul_ready)
			);
		end
		else begin : genblk1
			assign pcpi_mul_wr = 0;
			assign pcpi_mul_rd = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
			assign pcpi_mul_wait = 0;
			assign pcpi_mul_ready = 0;
		end
		if (ENABLE_DIV) begin : genblk2
			picorv32_pcpi_div pcpi_div(
				.clk(clk),
				.resetn(resetn),
				.pcpi_valid(pcpi_valid),
				.pcpi_insn(pcpi_insn),
				.pcpi_rs1(pcpi_rs1),
				.pcpi_rs2(pcpi_rs2),
				.pcpi_wr(pcpi_div_wr),
				.pcpi_rd(pcpi_div_rd),
				.pcpi_wait(pcpi_div_wait),
				.pcpi_ready(pcpi_div_ready)
			);
		end
		else begin : genblk2
			assign pcpi_div_wr = 0;
			assign pcpi_div_rd = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
			assign pcpi_div_wait = 0;
			assign pcpi_div_ready = 0;
		end
	endgenerate
	always @(*) begin
		pcpi_int_wr = 0;
		pcpi_int_rd = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
		pcpi_int_wait = |{ENABLE_PCPI && pcpi_wait, (ENABLE_MUL || ENABLE_FAST_MUL) && pcpi_mul_wait, ENABLE_DIV && pcpi_div_wait};
		pcpi_int_ready = |{ENABLE_PCPI && pcpi_ready, (ENABLE_MUL || ENABLE_FAST_MUL) && pcpi_mul_ready, ENABLE_DIV && pcpi_div_ready};
		(* parallel_case *)
		case (1'b1)
			ENABLE_PCPI && pcpi_ready: begin
				pcpi_int_wr = (ENABLE_PCPI ? pcpi_wr : 0);
				pcpi_int_rd = (ENABLE_PCPI ? pcpi_rd : 0);
			end
			(ENABLE_MUL || ENABLE_FAST_MUL) && pcpi_mul_ready: begin
				pcpi_int_wr = pcpi_mul_wr;
				pcpi_int_rd = pcpi_mul_rd;
			end
			ENABLE_DIV && pcpi_div_ready: begin
				pcpi_int_wr = pcpi_div_wr;
				pcpi_int_rd = pcpi_div_rd;
			end
		endcase
	end
	reg [1:0] mem_state;
	reg [1:0] mem_wordsize;
	reg [31:0] mem_rdata_word;
	reg [31:0] mem_rdata_q;
	reg mem_do_prefetch;
	reg mem_do_rinst;
	reg mem_do_rdata;
	reg mem_do_wdata;
	wire mem_xfer;
	reg mem_la_secondword;
	reg mem_la_firstword_reg;
	reg last_mem_valid;
	wire mem_la_firstword = ((COMPRESSED_ISA && (mem_do_prefetch || mem_do_rinst)) && next_pc[1]) && !mem_la_secondword;
	wire mem_la_firstword_xfer = (COMPRESSED_ISA && mem_xfer) && (!last_mem_valid ? mem_la_firstword : mem_la_firstword_reg);
	reg prefetched_high_word;
	reg clear_prefetched_high_word;
	reg [15:0] mem_16bit_buffer;
	wire [31:0] mem_rdata_latched_noshuffle;
	wire [31:0] mem_rdata_latched;
	wire mem_la_use_prefetched_high_word = ((COMPRESSED_ISA && mem_la_firstword) && prefetched_high_word) && !clear_prefetched_high_word;
	assign mem_xfer = (mem_valid && mem_ready) || (mem_la_use_prefetched_high_word && mem_do_rinst);
	wire mem_busy = |{mem_do_prefetch, mem_do_rinst, mem_do_rdata, mem_do_wdata};
	wire mem_done = (resetn && (((mem_xfer && |mem_state) && ((mem_do_rinst || mem_do_rdata) || mem_do_wdata)) || (&mem_state && mem_do_rinst))) && (!mem_la_firstword || (~&mem_rdata_latched[1:0] && mem_xfer));
	assign mem_la_write = (resetn && !mem_state) && mem_do_wdata;
	assign mem_la_read = resetn && (((!mem_la_use_prefetched_high_word && !mem_state) && ((mem_do_rinst || mem_do_prefetch) || mem_do_rdata)) || ((((COMPRESSED_ISA && mem_xfer) && (!last_mem_valid ? mem_la_firstword : mem_la_firstword_reg)) && !mem_la_secondword) && &mem_rdata_latched[1:0]));
	assign mem_la_addr = (mem_do_prefetch || mem_do_rinst ? {next_pc[31:2] + mem_la_firstword_xfer, 2'b00} : {reg_op1[31:2], 2'b00});
	assign mem_rdata_latched_noshuffle = (mem_xfer || LATCHED_MEM_RDATA ? mem_rdata : mem_rdata_q);
	assign mem_rdata_latched = (COMPRESSED_ISA && mem_la_use_prefetched_high_word ? {16'bxxxxxxxxxxxxxxxx, mem_16bit_buffer} : (COMPRESSED_ISA && mem_la_secondword ? {mem_rdata_latched_noshuffle[15:0], mem_16bit_buffer} : (COMPRESSED_ISA && mem_la_firstword ? {16'bxxxxxxxxxxxxxxxx, mem_rdata_latched_noshuffle[31:16]} : mem_rdata_latched_noshuffle)));
	always @(posedge clk)
		if (!resetn) begin
			mem_la_firstword_reg <= 0;
			last_mem_valid <= 0;
		end
		else begin
			if (!last_mem_valid)
				mem_la_firstword_reg <= mem_la_firstword;
			last_mem_valid <= mem_valid && !mem_ready;
		end
	always @(*)
		(* full_case *)
		case (mem_wordsize)
			0: begin
				mem_la_wdata = reg_op2;
				mem_la_wstrb = 4'b1111;
				mem_rdata_word = mem_rdata;
			end
			1: begin
				mem_la_wdata = {2 {reg_op2[15:0]}};
				mem_la_wstrb = (reg_op1[1] ? 4'b1100 : 4'b0011);
				case (reg_op1[1])
					1'b0: mem_rdata_word = {16'b0000000000000000, mem_rdata[15:0]};
					1'b1: mem_rdata_word = {16'b0000000000000000, mem_rdata[31:16]};
				endcase
			end
			2: begin
				mem_la_wdata = {4 {reg_op2[7:0]}};
				mem_la_wstrb = 4'b0001 << reg_op1[1:0];
				case (reg_op1[1:0])
					2'b00: mem_rdata_word = {24'b000000000000000000000000, mem_rdata[7:0]};
					2'b01: mem_rdata_word = {24'b000000000000000000000000, mem_rdata[15:8]};
					2'b10: mem_rdata_word = {24'b000000000000000000000000, mem_rdata[23:16]};
					2'b11: mem_rdata_word = {24'b000000000000000000000000, mem_rdata[31:24]};
				endcase
			end
		endcase
	always @(posedge clk) begin
		if (mem_xfer) begin
			mem_rdata_q <= (COMPRESSED_ISA ? mem_rdata_latched : mem_rdata);
			next_insn_opcode <= (COMPRESSED_ISA ? mem_rdata_latched : mem_rdata);
		end
		if ((COMPRESSED_ISA && mem_done) && (mem_do_prefetch || mem_do_rinst))
			case (mem_rdata_latched[1:0])
				2'b00:
					case (mem_rdata_latched[15:13])
						3'b000: begin
							mem_rdata_q[14:12] <= 3'b000;
							mem_rdata_q[31:20] <= {2'b00, mem_rdata_latched[10:7], mem_rdata_latched[12:11], mem_rdata_latched[5], mem_rdata_latched[6], 2'b00};
						end
						3'b010: begin
							mem_rdata_q[31:20] <= {5'b00000, mem_rdata_latched[5], mem_rdata_latched[12:10], mem_rdata_latched[6], 2'b00};
							mem_rdata_q[14:12] <= 3'b010;
						end
						3'b110: begin
							{mem_rdata_q[31:25], mem_rdata_q[11:7]} <= {5'b00000, mem_rdata_latched[5], mem_rdata_latched[12:10], mem_rdata_latched[6], 2'b00};
							mem_rdata_q[14:12] <= 3'b010;
						end
					endcase
				2'b01:
					case (mem_rdata_latched[15:13])
						3'b000: begin
							mem_rdata_q[14:12] <= 3'b000;
							mem_rdata_q[31:20] <= $signed({mem_rdata_latched[12], mem_rdata_latched[6:2]});
						end
						3'b010: begin
							mem_rdata_q[14:12] <= 3'b000;
							mem_rdata_q[31:20] <= $signed({mem_rdata_latched[12], mem_rdata_latched[6:2]});
						end
						3'b011:
							if (mem_rdata_latched[11:7] == 2) begin
								mem_rdata_q[14:12] <= 3'b000;
								mem_rdata_q[31:20] <= $signed({mem_rdata_latched[12], mem_rdata_latched[4:3], mem_rdata_latched[5], mem_rdata_latched[2], mem_rdata_latched[6], 4'b0000});
							end
							else
								mem_rdata_q[31:12] <= $signed({mem_rdata_latched[12], mem_rdata_latched[6:2]});
						3'b100: begin
							if (mem_rdata_latched[11:10] == 2'b00) begin
								mem_rdata_q[31:25] <= 7'b0000000;
								mem_rdata_q[14:12] <= 3'b101;
							end
							if (mem_rdata_latched[11:10] == 2'b01) begin
								mem_rdata_q[31:25] <= 7'b0100000;
								mem_rdata_q[14:12] <= 3'b101;
							end
							if (mem_rdata_latched[11:10] == 2'b10) begin
								mem_rdata_q[14:12] <= 3'b111;
								mem_rdata_q[31:20] <= $signed({mem_rdata_latched[12], mem_rdata_latched[6:2]});
							end
							if (mem_rdata_latched[12:10] == 3'b011) begin
								if (mem_rdata_latched[6:5] == 2'b00)
									mem_rdata_q[14:12] <= 3'b000;
								if (mem_rdata_latched[6:5] == 2'b01)
									mem_rdata_q[14:12] <= 3'b100;
								if (mem_rdata_latched[6:5] == 2'b10)
									mem_rdata_q[14:12] <= 3'b110;
								if (mem_rdata_latched[6:5] == 2'b11)
									mem_rdata_q[14:12] <= 3'b111;
								mem_rdata_q[31:25] <= (mem_rdata_latched[6:5] == 2'b00 ? 7'b0100000 : 7'b0000000);
							end
						end
						3'b110: begin
							mem_rdata_q[14:12] <= 3'b000;
							{mem_rdata_q[31], mem_rdata_q[7], mem_rdata_q[30:25], mem_rdata_q[11:8]} <= $signed({mem_rdata_latched[12], mem_rdata_latched[6:5], mem_rdata_latched[2], mem_rdata_latched[11:10], mem_rdata_latched[4:3]});
						end
						3'b111: begin
							mem_rdata_q[14:12] <= 3'b001;
							{mem_rdata_q[31], mem_rdata_q[7], mem_rdata_q[30:25], mem_rdata_q[11:8]} <= $signed({mem_rdata_latched[12], mem_rdata_latched[6:5], mem_rdata_latched[2], mem_rdata_latched[11:10], mem_rdata_latched[4:3]});
						end
					endcase
				2'b10:
					case (mem_rdata_latched[15:13])
						3'b000: begin
							mem_rdata_q[31:25] <= 7'b0000000;
							mem_rdata_q[14:12] <= 3'b001;
						end
						3'b010: begin
							mem_rdata_q[31:20] <= {4'b0000, mem_rdata_latched[3:2], mem_rdata_latched[12], mem_rdata_latched[6:4], 2'b00};
							mem_rdata_q[14:12] <= 3'b010;
						end
						3'b100: begin
							if ((mem_rdata_latched[12] == 0) && (mem_rdata_latched[6:2] == 0)) begin
								mem_rdata_q[14:12] <= 3'b000;
								mem_rdata_q[31:20] <= 12'b000000000000;
							end
							if ((mem_rdata_latched[12] == 0) && (mem_rdata_latched[6:2] != 0)) begin
								mem_rdata_q[14:12] <= 3'b000;
								mem_rdata_q[31:25] <= 7'b0000000;
							end
							if (((mem_rdata_latched[12] != 0) && (mem_rdata_latched[11:7] != 0)) && (mem_rdata_latched[6:2] == 0)) begin
								mem_rdata_q[14:12] <= 3'b000;
								mem_rdata_q[31:20] <= 12'b000000000000;
							end
							if ((mem_rdata_latched[12] != 0) && (mem_rdata_latched[6:2] != 0)) begin
								mem_rdata_q[14:12] <= 3'b000;
								mem_rdata_q[31:25] <= 7'b0000000;
							end
						end
						3'b110: begin
							{mem_rdata_q[31:25], mem_rdata_q[11:7]} <= {4'b0000, mem_rdata_latched[8:7], mem_rdata_latched[12:9], 2'b00};
							mem_rdata_q[14:12] <= 3'b010;
						end
					endcase
			endcase
	end
	always @(posedge clk)
		if (resetn && !trap) begin
			if ((mem_do_prefetch || mem_do_rinst) || mem_do_rdata)
				empty_statement;
			if (mem_do_prefetch || mem_do_rinst)
				empty_statement;
			if (mem_do_rdata)
				empty_statement;
			if (mem_do_wdata)
				empty_statement;
			if ((mem_state == 2) || (mem_state == 3))
				empty_statement;
		end
	always @(posedge clk) begin
		if (!resetn || trap) begin
			if (!resetn)
				mem_state <= 0;
			if (!resetn || mem_ready)
				mem_valid <= 0;
			mem_la_secondword <= 0;
			prefetched_high_word <= 0;
		end
		else begin
			if (mem_la_read || mem_la_write) begin
				mem_addr <= mem_la_addr;
				mem_wstrb <= mem_la_wstrb & {4 {mem_la_write}};
			end
			if (mem_la_write)
				mem_wdata <= mem_la_wdata;
			case (mem_state)
				0: begin
					if ((mem_do_prefetch || mem_do_rinst) || mem_do_rdata) begin
						mem_valid <= !mem_la_use_prefetched_high_word;
						mem_instr <= mem_do_prefetch || mem_do_rinst;
						mem_wstrb <= 0;
						mem_state <= 1;
					end
					if (mem_do_wdata) begin
						mem_valid <= 1;
						mem_instr <= 0;
						mem_state <= 2;
					end
				end
				1: begin
					empty_statement;
					empty_statement;
					empty_statement;
					empty_statement;
					if (mem_xfer) begin
						if (COMPRESSED_ISA && mem_la_read) begin
							mem_valid <= 1;
							mem_la_secondword <= 1;
							if (!mem_la_use_prefetched_high_word)
								mem_16bit_buffer <= mem_rdata[31:16];
						end
						else begin
							mem_valid <= 0;
							mem_la_secondword <= 0;
							if (COMPRESSED_ISA && !mem_do_rdata) begin
								if (~&mem_rdata[1:0] || mem_la_secondword) begin
									mem_16bit_buffer <= mem_rdata[31:16];
									prefetched_high_word <= 1;
								end
								else
									prefetched_high_word <= 0;
							end
							mem_state <= (mem_do_rinst || mem_do_rdata ? 0 : 3);
						end
					end
				end
				2: begin
					empty_statement;
					empty_statement;
					if (mem_xfer) begin
						mem_valid <= 0;
						mem_state <= 0;
					end
				end
				3: begin
					empty_statement;
					empty_statement;
					if (mem_do_rinst)
						mem_state <= 0;
				end
			endcase
		end
		if (clear_prefetched_high_word)
			prefetched_high_word <= 0;
	end
	reg instr_lui;
	reg instr_auipc;
	reg instr_jal;
	reg instr_jalr;
	reg instr_beq;
	reg instr_bne;
	reg instr_blt;
	reg instr_bge;
	reg instr_bltu;
	reg instr_bgeu;
	reg instr_lb;
	reg instr_lh;
	reg instr_lw;
	reg instr_lbu;
	reg instr_lhu;
	reg instr_sb;
	reg instr_sh;
	reg instr_sw;
	reg instr_addi;
	reg instr_slti;
	reg instr_sltiu;
	reg instr_xori;
	reg instr_ori;
	reg instr_andi;
	reg instr_slli;
	reg instr_srli;
	reg instr_srai;
	reg instr_add;
	reg instr_sub;
	reg instr_sll;
	reg instr_slt;
	reg instr_sltu;
	reg instr_xor;
	reg instr_srl;
	reg instr_sra;
	reg instr_or;
	reg instr_and;
	reg instr_rdcycle;
	reg instr_rdcycleh;
	reg instr_rdinstr;
	reg instr_rdinstrh;
	reg instr_ecall_ebreak;
	reg instr_getq;
	reg instr_setq;
	reg instr_retirq;
	reg instr_maskirq;
	reg instr_waitirq;
	reg instr_timer;
	wire instr_trap;
	reg [regindex_bits - 1:0] decoded_rd;
	reg [regindex_bits - 1:0] decoded_rs1;
	reg [regindex_bits - 1:0] decoded_rs2;
	reg [31:0] decoded_imm;
	reg [31:0] decoded_imm_j;
	reg decoder_trigger;
	reg decoder_trigger_q;
	reg decoder_pseudo_trigger;
	reg decoder_pseudo_trigger_q;
	reg compressed_instr;
	reg is_lui_auipc_jal;
	reg is_lb_lh_lw_lbu_lhu;
	reg is_slli_srli_srai;
	reg is_jalr_addi_slti_sltiu_xori_ori_andi;
	reg is_sb_sh_sw;
	reg is_sll_srl_sra;
	reg is_lui_auipc_jal_jalr_addi_add_sub;
	reg is_slti_blt_slt;
	reg is_sltiu_bltu_sltu;
	reg is_beq_bne_blt_bge_bltu_bgeu;
	reg is_lbu_lhu_lw;
	reg is_alu_reg_imm;
	reg is_alu_reg_reg;
	reg is_compare;
	assign instr_trap = (CATCH_ILLINSN || WITH_PCPI) && !{instr_lui, instr_auipc, instr_jal, instr_jalr, instr_beq, instr_bne, instr_blt, instr_bge, instr_bltu, instr_bgeu, instr_lb, instr_lh, instr_lw, instr_lbu, instr_lhu, instr_sb, instr_sh, instr_sw, instr_addi, instr_slti, instr_sltiu, instr_xori, instr_ori, instr_andi, instr_slli, instr_srli, instr_srai, instr_add, instr_sub, instr_sll, instr_slt, instr_sltu, instr_xor, instr_srl, instr_sra, instr_or, instr_and, instr_rdcycle, instr_rdcycleh, instr_rdinstr, instr_rdinstrh, instr_getq, instr_setq, instr_retirq, instr_maskirq, instr_waitirq, instr_timer};
	wire is_rdcycle_rdcycleh_rdinstr_rdinstrh;
	assign is_rdcycle_rdcycleh_rdinstr_rdinstrh = |{instr_rdcycle, instr_rdcycleh, instr_rdinstr, instr_rdinstrh};
	reg [63:0] new_ascii_instr;
	reg [63:0] dbg_ascii_instr;
	reg [31:0] dbg_insn_imm;
	reg [4:0] dbg_insn_rs1;
	reg [4:0] dbg_insn_rs2;
	reg [4:0] dbg_insn_rd;
	reg [31:0] dbg_rs1val;
	reg [31:0] dbg_rs2val;
	reg dbg_rs1val_valid;
	reg dbg_rs2val_valid;
	always @(*) begin
		new_ascii_instr = "";
		if (instr_lui)
			new_ascii_instr = "lui";
		if (instr_auipc)
			new_ascii_instr = "auipc";
		if (instr_jal)
			new_ascii_instr = "jal";
		if (instr_jalr)
			new_ascii_instr = "jalr";
		if (instr_beq)
			new_ascii_instr = "beq";
		if (instr_bne)
			new_ascii_instr = "bne";
		if (instr_blt)
			new_ascii_instr = "blt";
		if (instr_bge)
			new_ascii_instr = "bge";
		if (instr_bltu)
			new_ascii_instr = "bltu";
		if (instr_bgeu)
			new_ascii_instr = "bgeu";
		if (instr_lb)
			new_ascii_instr = "lb";
		if (instr_lh)
			new_ascii_instr = "lh";
		if (instr_lw)
			new_ascii_instr = "lw";
		if (instr_lbu)
			new_ascii_instr = "lbu";
		if (instr_lhu)
			new_ascii_instr = "lhu";
		if (instr_sb)
			new_ascii_instr = "sb";
		if (instr_sh)
			new_ascii_instr = "sh";
		if (instr_sw)
			new_ascii_instr = "sw";
		if (instr_addi)
			new_ascii_instr = "addi";
		if (instr_slti)
			new_ascii_instr = "slti";
		if (instr_sltiu)
			new_ascii_instr = "sltiu";
		if (instr_xori)
			new_ascii_instr = "xori";
		if (instr_ori)
			new_ascii_instr = "ori";
		if (instr_andi)
			new_ascii_instr = "andi";
		if (instr_slli)
			new_ascii_instr = "slli";
		if (instr_srli)
			new_ascii_instr = "srli";
		if (instr_srai)
			new_ascii_instr = "srai";
		if (instr_add)
			new_ascii_instr = "add";
		if (instr_sub)
			new_ascii_instr = "sub";
		if (instr_sll)
			new_ascii_instr = "sll";
		if (instr_slt)
			new_ascii_instr = "slt";
		if (instr_sltu)
			new_ascii_instr = "sltu";
		if (instr_xor)
			new_ascii_instr = "xor";
		if (instr_srl)
			new_ascii_instr = "srl";
		if (instr_sra)
			new_ascii_instr = "sra";
		if (instr_or)
			new_ascii_instr = "or";
		if (instr_and)
			new_ascii_instr = "and";
		if (instr_rdcycle)
			new_ascii_instr = "rdcycle";
		if (instr_rdcycleh)
			new_ascii_instr = "rdcycleh";
		if (instr_rdinstr)
			new_ascii_instr = "rdinstr";
		if (instr_rdinstrh)
			new_ascii_instr = "rdinstrh";
		if (instr_getq)
			new_ascii_instr = "getq";
		if (instr_setq)
			new_ascii_instr = "setq";
		if (instr_retirq)
			new_ascii_instr = "retirq";
		if (instr_maskirq)
			new_ascii_instr = "maskirq";
		if (instr_waitirq)
			new_ascii_instr = "waitirq";
		if (instr_timer)
			new_ascii_instr = "timer";
	end
	reg [63:0] q_ascii_instr;
	reg [31:0] q_insn_imm;
	reg [31:0] q_insn_opcode;
	reg [4:0] q_insn_rs1;
	reg [4:0] q_insn_rs2;
	reg [4:0] q_insn_rd;
	reg dbg_next;
	wire launch_next_insn;
	reg dbg_valid_insn;
	reg [63:0] cached_ascii_instr;
	reg [31:0] cached_insn_imm;
	reg [31:0] cached_insn_opcode;
	reg [4:0] cached_insn_rs1;
	reg [4:0] cached_insn_rs2;
	reg [4:0] cached_insn_rd;
	always @(posedge clk) begin
		q_ascii_instr <= dbg_ascii_instr;
		q_insn_imm <= dbg_insn_imm;
		q_insn_opcode <= dbg_insn_opcode;
		q_insn_rs1 <= dbg_insn_rs1;
		q_insn_rs2 <= dbg_insn_rs2;
		q_insn_rd <= dbg_insn_rd;
		dbg_next <= launch_next_insn;
		if (!resetn || trap)
			dbg_valid_insn <= 0;
		else if (launch_next_insn)
			dbg_valid_insn <= 1;
		if (decoder_trigger_q) begin
			cached_ascii_instr <= new_ascii_instr;
			cached_insn_imm <= decoded_imm;
			if (&next_insn_opcode[1:0])
				cached_insn_opcode <= next_insn_opcode;
			else
				cached_insn_opcode <= {16'b0000000000000000, next_insn_opcode[15:0]};
			cached_insn_rs1 <= decoded_rs1;
			cached_insn_rs2 <= decoded_rs2;
			cached_insn_rd <= decoded_rd;
		end
		if (launch_next_insn)
			dbg_insn_addr <= next_pc;
	end
	always @(*) begin
		dbg_ascii_instr = q_ascii_instr;
		dbg_insn_imm = q_insn_imm;
		dbg_insn_opcode = q_insn_opcode;
		dbg_insn_rs1 = q_insn_rs1;
		dbg_insn_rs2 = q_insn_rs2;
		dbg_insn_rd = q_insn_rd;
		if (dbg_next) begin
			if (decoder_pseudo_trigger_q) begin
				dbg_ascii_instr = cached_ascii_instr;
				dbg_insn_imm = cached_insn_imm;
				dbg_insn_opcode = cached_insn_opcode;
				dbg_insn_rs1 = cached_insn_rs1;
				dbg_insn_rs2 = cached_insn_rs2;
				dbg_insn_rd = cached_insn_rd;
			end
			else begin
				dbg_ascii_instr = new_ascii_instr;
				if (&next_insn_opcode[1:0])
					dbg_insn_opcode = next_insn_opcode;
				else
					dbg_insn_opcode = {16'b0000000000000000, next_insn_opcode[15:0]};
				dbg_insn_imm = decoded_imm;
				dbg_insn_rs1 = decoded_rs1;
				dbg_insn_rs2 = decoded_rs2;
				dbg_insn_rd = decoded_rd;
			end
		end
	end
	always @(posedge clk) begin
		is_lui_auipc_jal <= |{instr_lui, instr_auipc, instr_jal};
		is_lui_auipc_jal_jalr_addi_add_sub <= |{instr_lui, instr_auipc, instr_jal, instr_jalr, instr_addi, instr_add, instr_sub};
		is_slti_blt_slt <= |{instr_slti, instr_blt, instr_slt};
		is_sltiu_bltu_sltu <= |{instr_sltiu, instr_bltu, instr_sltu};
		is_lbu_lhu_lw <= |{instr_lbu, instr_lhu, instr_lw};
		is_compare <= |{is_beq_bne_blt_bge_bltu_bgeu, instr_slti, instr_slt, instr_sltiu, instr_sltu};
		if (mem_do_rinst && mem_done) begin
			instr_lui <= mem_rdata_latched[6:0] == 7'b0110111;
			instr_auipc <= mem_rdata_latched[6:0] == 7'b0010111;
			instr_jal <= mem_rdata_latched[6:0] == 7'b1101111;
			instr_jalr <= (mem_rdata_latched[6:0] == 7'b1100111) && (mem_rdata_latched[14:12] == 3'b000);
			instr_retirq <= ((mem_rdata_latched[6:0] == 7'b0001011) && (mem_rdata_latched[31:25] == 7'b0000010)) && ENABLE_IRQ;
			instr_waitirq <= ((mem_rdata_latched[6:0] == 7'b0001011) && (mem_rdata_latched[31:25] == 7'b0000100)) && ENABLE_IRQ;
			is_beq_bne_blt_bge_bltu_bgeu <= mem_rdata_latched[6:0] == 7'b1100011;
			is_lb_lh_lw_lbu_lhu <= mem_rdata_latched[6:0] == 7'b0000011;
			is_sb_sh_sw <= mem_rdata_latched[6:0] == 7'b0100011;
			is_alu_reg_imm <= mem_rdata_latched[6:0] == 7'b0010011;
			is_alu_reg_reg <= mem_rdata_latched[6:0] == 7'b0110011;
			{decoded_imm_j[31:20], decoded_imm_j[10:1], decoded_imm_j[11], decoded_imm_j[19:12], decoded_imm_j[0]} <= $signed({mem_rdata_latched[31:12], 1'b0});
			decoded_rd <= mem_rdata_latched[11:7];
			decoded_rs1 <= mem_rdata_latched[19:15];
			decoded_rs2 <= mem_rdata_latched[24:20];
			if ((((mem_rdata_latched[6:0] == 7'b0001011) && (mem_rdata_latched[31:25] == 7'b0000000)) && ENABLE_IRQ) && ENABLE_IRQ_QREGS)
				decoded_rs1[regindex_bits - 1] <= 1;
			if (((mem_rdata_latched[6:0] == 7'b0001011) && (mem_rdata_latched[31:25] == 7'b0000010)) && ENABLE_IRQ)
				decoded_rs1 <= (ENABLE_IRQ_QREGS ? irqregs_offset : 3);
			compressed_instr <= 0;
			if (COMPRESSED_ISA && (mem_rdata_latched[1:0] != 2'b11)) begin
				compressed_instr <= 1;
				decoded_rd <= 0;
				decoded_rs1 <= 0;
				decoded_rs2 <= 0;
				{decoded_imm_j[31:11], decoded_imm_j[4], decoded_imm_j[9:8], decoded_imm_j[10], decoded_imm_j[6], decoded_imm_j[7], decoded_imm_j[3:1], decoded_imm_j[5], decoded_imm_j[0]} <= $signed({mem_rdata_latched[12:2], 1'b0});
				case (mem_rdata_latched[1:0])
					2'b00:
						case (mem_rdata_latched[15:13])
							3'b000: begin
								is_alu_reg_imm <= |mem_rdata_latched[12:5];
								decoded_rs1 <= 2;
								decoded_rd <= 8 + mem_rdata_latched[4:2];
							end
							3'b010: begin
								is_lb_lh_lw_lbu_lhu <= 1;
								decoded_rs1 <= 8 + mem_rdata_latched[9:7];
								decoded_rd <= 8 + mem_rdata_latched[4:2];
							end
							3'b110: begin
								is_sb_sh_sw <= 1;
								decoded_rs1 <= 8 + mem_rdata_latched[9:7];
								decoded_rs2 <= 8 + mem_rdata_latched[4:2];
							end
						endcase
					2'b01:
						case (mem_rdata_latched[15:13])
							3'b000: begin
								is_alu_reg_imm <= 1;
								decoded_rd <= mem_rdata_latched[11:7];
								decoded_rs1 <= mem_rdata_latched[11:7];
							end
							3'b001: begin
								instr_jal <= 1;
								decoded_rd <= 1;
							end
							3'b010: begin
								is_alu_reg_imm <= 1;
								decoded_rd <= mem_rdata_latched[11:7];
								decoded_rs1 <= 0;
							end
							3'b011:
								if (mem_rdata_latched[12] || mem_rdata_latched[6:2]) begin
									if (mem_rdata_latched[11:7] == 2) begin
										is_alu_reg_imm <= 1;
										decoded_rd <= mem_rdata_latched[11:7];
										decoded_rs1 <= mem_rdata_latched[11:7];
									end
									else begin
										instr_lui <= 1;
										decoded_rd <= mem_rdata_latched[11:7];
										decoded_rs1 <= 0;
									end
								end
							3'b100: begin
								if (!mem_rdata_latched[11] && !mem_rdata_latched[12]) begin
									is_alu_reg_imm <= 1;
									decoded_rd <= 8 + mem_rdata_latched[9:7];
									decoded_rs1 <= 8 + mem_rdata_latched[9:7];
									decoded_rs2 <= {mem_rdata_latched[12], mem_rdata_latched[6:2]};
								end
								if (mem_rdata_latched[11:10] == 2'b10) begin
									is_alu_reg_imm <= 1;
									decoded_rd <= 8 + mem_rdata_latched[9:7];
									decoded_rs1 <= 8 + mem_rdata_latched[9:7];
								end
								if (mem_rdata_latched[12:10] == 3'b011) begin
									is_alu_reg_reg <= 1;
									decoded_rd <= 8 + mem_rdata_latched[9:7];
									decoded_rs1 <= 8 + mem_rdata_latched[9:7];
									decoded_rs2 <= 8 + mem_rdata_latched[4:2];
								end
							end
							3'b101: instr_jal <= 1;
							3'b110: begin
								is_beq_bne_blt_bge_bltu_bgeu <= 1;
								decoded_rs1 <= 8 + mem_rdata_latched[9:7];
								decoded_rs2 <= 0;
							end
							3'b111: begin
								is_beq_bne_blt_bge_bltu_bgeu <= 1;
								decoded_rs1 <= 8 + mem_rdata_latched[9:7];
								decoded_rs2 <= 0;
							end
						endcase
					2'b10:
						case (mem_rdata_latched[15:13])
							3'b000:
								if (!mem_rdata_latched[12]) begin
									is_alu_reg_imm <= 1;
									decoded_rd <= mem_rdata_latched[11:7];
									decoded_rs1 <= mem_rdata_latched[11:7];
									decoded_rs2 <= {mem_rdata_latched[12], mem_rdata_latched[6:2]};
								end
							3'b010:
								if (mem_rdata_latched[11:7]) begin
									is_lb_lh_lw_lbu_lhu <= 1;
									decoded_rd <= mem_rdata_latched[11:7];
									decoded_rs1 <= 2;
								end
							3'b100: begin
								if (((mem_rdata_latched[12] == 0) && (mem_rdata_latched[11:7] != 0)) && (mem_rdata_latched[6:2] == 0)) begin
									instr_jalr <= 1;
									decoded_rd <= 0;
									decoded_rs1 <= mem_rdata_latched[11:7];
								end
								if ((mem_rdata_latched[12] == 0) && (mem_rdata_latched[6:2] != 0)) begin
									is_alu_reg_reg <= 1;
									decoded_rd <= mem_rdata_latched[11:7];
									decoded_rs1 <= 0;
									decoded_rs2 <= mem_rdata_latched[6:2];
								end
								if (((mem_rdata_latched[12] != 0) && (mem_rdata_latched[11:7] != 0)) && (mem_rdata_latched[6:2] == 0)) begin
									instr_jalr <= 1;
									decoded_rd <= 1;
									decoded_rs1 <= mem_rdata_latched[11:7];
								end
								if ((mem_rdata_latched[12] != 0) && (mem_rdata_latched[6:2] != 0)) begin
									is_alu_reg_reg <= 1;
									decoded_rd <= mem_rdata_latched[11:7];
									decoded_rs1 <= mem_rdata_latched[11:7];
									decoded_rs2 <= mem_rdata_latched[6:2];
								end
							end
							3'b110: begin
								is_sb_sh_sw <= 1;
								decoded_rs1 <= 2;
								decoded_rs2 <= mem_rdata_latched[6:2];
							end
						endcase
				endcase
			end
		end
		if (decoder_trigger && !decoder_pseudo_trigger) begin
			pcpi_insn <= (WITH_PCPI ? mem_rdata_q : 'bx);
			instr_beq <= is_beq_bne_blt_bge_bltu_bgeu && (mem_rdata_q[14:12] == 3'b000);
			instr_bne <= is_beq_bne_blt_bge_bltu_bgeu && (mem_rdata_q[14:12] == 3'b001);
			instr_blt <= is_beq_bne_blt_bge_bltu_bgeu && (mem_rdata_q[14:12] == 3'b100);
			instr_bge <= is_beq_bne_blt_bge_bltu_bgeu && (mem_rdata_q[14:12] == 3'b101);
			instr_bltu <= is_beq_bne_blt_bge_bltu_bgeu && (mem_rdata_q[14:12] == 3'b110);
			instr_bgeu <= is_beq_bne_blt_bge_bltu_bgeu && (mem_rdata_q[14:12] == 3'b111);
			instr_lb <= is_lb_lh_lw_lbu_lhu && (mem_rdata_q[14:12] == 3'b000);
			instr_lh <= is_lb_lh_lw_lbu_lhu && (mem_rdata_q[14:12] == 3'b001);
			instr_lw <= is_lb_lh_lw_lbu_lhu && (mem_rdata_q[14:12] == 3'b010);
			instr_lbu <= is_lb_lh_lw_lbu_lhu && (mem_rdata_q[14:12] == 3'b100);
			instr_lhu <= is_lb_lh_lw_lbu_lhu && (mem_rdata_q[14:12] == 3'b101);
			instr_sb <= is_sb_sh_sw && (mem_rdata_q[14:12] == 3'b000);
			instr_sh <= is_sb_sh_sw && (mem_rdata_q[14:12] == 3'b001);
			instr_sw <= is_sb_sh_sw && (mem_rdata_q[14:12] == 3'b010);
			instr_addi <= is_alu_reg_imm && (mem_rdata_q[14:12] == 3'b000);
			instr_slti <= is_alu_reg_imm && (mem_rdata_q[14:12] == 3'b010);
			instr_sltiu <= is_alu_reg_imm && (mem_rdata_q[14:12] == 3'b011);
			instr_xori <= is_alu_reg_imm && (mem_rdata_q[14:12] == 3'b100);
			instr_ori <= is_alu_reg_imm && (mem_rdata_q[14:12] == 3'b110);
			instr_andi <= is_alu_reg_imm && (mem_rdata_q[14:12] == 3'b111);
			instr_slli <= (is_alu_reg_imm && (mem_rdata_q[14:12] == 3'b001)) && (mem_rdata_q[31:25] == 7'b0000000);
			instr_srli <= (is_alu_reg_imm && (mem_rdata_q[14:12] == 3'b101)) && (mem_rdata_q[31:25] == 7'b0000000);
			instr_srai <= (is_alu_reg_imm && (mem_rdata_q[14:12] == 3'b101)) && (mem_rdata_q[31:25] == 7'b0100000);
			instr_add <= (is_alu_reg_reg && (mem_rdata_q[14:12] == 3'b000)) && (mem_rdata_q[31:25] == 7'b0000000);
			instr_sub <= (is_alu_reg_reg && (mem_rdata_q[14:12] == 3'b000)) && (mem_rdata_q[31:25] == 7'b0100000);
			instr_sll <= (is_alu_reg_reg && (mem_rdata_q[14:12] == 3'b001)) && (mem_rdata_q[31:25] == 7'b0000000);
			instr_slt <= (is_alu_reg_reg && (mem_rdata_q[14:12] == 3'b010)) && (mem_rdata_q[31:25] == 7'b0000000);
			instr_sltu <= (is_alu_reg_reg && (mem_rdata_q[14:12] == 3'b011)) && (mem_rdata_q[31:25] == 7'b0000000);
			instr_xor <= (is_alu_reg_reg && (mem_rdata_q[14:12] == 3'b100)) && (mem_rdata_q[31:25] == 7'b0000000);
			instr_srl <= (is_alu_reg_reg && (mem_rdata_q[14:12] == 3'b101)) && (mem_rdata_q[31:25] == 7'b0000000);
			instr_sra <= (is_alu_reg_reg && (mem_rdata_q[14:12] == 3'b101)) && (mem_rdata_q[31:25] == 7'b0100000);
			instr_or <= (is_alu_reg_reg && (mem_rdata_q[14:12] == 3'b110)) && (mem_rdata_q[31:25] == 7'b0000000);
			instr_and <= (is_alu_reg_reg && (mem_rdata_q[14:12] == 3'b111)) && (mem_rdata_q[31:25] == 7'b0000000);
			instr_rdcycle <= (((mem_rdata_q[6:0] == 7'b1110011) && (mem_rdata_q[31:12] == 'b11000000000000000010)) || ((mem_rdata_q[6:0] == 7'b1110011) && (mem_rdata_q[31:12] == 'b11000000000100000010))) && ENABLE_COUNTERS;
			instr_rdcycleh <= ((((mem_rdata_q[6:0] == 7'b1110011) && (mem_rdata_q[31:12] == 'b11001000000000000010)) || ((mem_rdata_q[6:0] == 7'b1110011) && (mem_rdata_q[31:12] == 'b11001000000100000010))) && ENABLE_COUNTERS) && ENABLE_COUNTERS64;
			instr_rdinstr <= ((mem_rdata_q[6:0] == 7'b1110011) && (mem_rdata_q[31:12] == 'b11000000001000000010)) && ENABLE_COUNTERS;
			instr_rdinstrh <= (((mem_rdata_q[6:0] == 7'b1110011) && (mem_rdata_q[31:12] == 'b11001000001000000010)) && ENABLE_COUNTERS) && ENABLE_COUNTERS64;
			instr_ecall_ebreak <= (((mem_rdata_q[6:0] == 7'b1110011) && !mem_rdata_q[31:21]) && !mem_rdata_q[19:7]) || (COMPRESSED_ISA && (mem_rdata_q[15:0] == 16'h9002));
			instr_getq <= (((mem_rdata_q[6:0] == 7'b0001011) && (mem_rdata_q[31:25] == 7'b0000000)) && ENABLE_IRQ) && ENABLE_IRQ_QREGS;
			instr_setq <= (((mem_rdata_q[6:0] == 7'b0001011) && (mem_rdata_q[31:25] == 7'b0000001)) && ENABLE_IRQ) && ENABLE_IRQ_QREGS;
			instr_maskirq <= ((mem_rdata_q[6:0] == 7'b0001011) && (mem_rdata_q[31:25] == 7'b0000011)) && ENABLE_IRQ;
			instr_timer <= (((mem_rdata_q[6:0] == 7'b0001011) && (mem_rdata_q[31:25] == 7'b0000101)) && ENABLE_IRQ) && ENABLE_IRQ_TIMER;
			is_slli_srli_srai <= is_alu_reg_imm && |{(mem_rdata_q[14:12] == 3'b001) && (mem_rdata_q[31:25] == 7'b0000000), (mem_rdata_q[14:12] == 3'b101) && (mem_rdata_q[31:25] == 7'b0000000), (mem_rdata_q[14:12] == 3'b101) && (mem_rdata_q[31:25] == 7'b0100000)};
			is_jalr_addi_slti_sltiu_xori_ori_andi <= instr_jalr || (is_alu_reg_imm && |{mem_rdata_q[14:12] == 3'b000, mem_rdata_q[14:12] == 3'b010, mem_rdata_q[14:12] == 3'b011, mem_rdata_q[14:12] == 3'b100, mem_rdata_q[14:12] == 3'b110, mem_rdata_q[14:12] == 3'b111});
			is_sll_srl_sra <= is_alu_reg_reg && |{(mem_rdata_q[14:12] == 3'b001) && (mem_rdata_q[31:25] == 7'b0000000), (mem_rdata_q[14:12] == 3'b101) && (mem_rdata_q[31:25] == 7'b0000000), (mem_rdata_q[14:12] == 3'b101) && (mem_rdata_q[31:25] == 7'b0100000)};
			is_lui_auipc_jal_jalr_addi_add_sub <= 0;
			is_compare <= 0;
			(* parallel_case *)
			case (1'b1)
				instr_jal: decoded_imm <= decoded_imm_j;
				|{instr_lui, instr_auipc}: decoded_imm <= mem_rdata_q[31:12] << 12;
				|{instr_jalr, is_lb_lh_lw_lbu_lhu, is_alu_reg_imm}: decoded_imm <= $signed(mem_rdata_q[31:20]);
				is_beq_bne_blt_bge_bltu_bgeu: decoded_imm <= $signed({mem_rdata_q[31], mem_rdata_q[7], mem_rdata_q[30:25], mem_rdata_q[11:8], 1'b0});
				is_sb_sh_sw: decoded_imm <= $signed({mem_rdata_q[31:25], mem_rdata_q[11:7]});
				default: decoded_imm <= 1'bx;
			endcase
		end
		if (!resetn) begin
			is_beq_bne_blt_bge_bltu_bgeu <= 0;
			is_compare <= 0;
			instr_beq <= 0;
			instr_bne <= 0;
			instr_blt <= 0;
			instr_bge <= 0;
			instr_bltu <= 0;
			instr_bgeu <= 0;
			instr_addi <= 0;
			instr_slti <= 0;
			instr_sltiu <= 0;
			instr_xori <= 0;
			instr_ori <= 0;
			instr_andi <= 0;
			instr_add <= 0;
			instr_sub <= 0;
			instr_sll <= 0;
			instr_slt <= 0;
			instr_sltu <= 0;
			instr_xor <= 0;
			instr_srl <= 0;
			instr_sra <= 0;
			instr_or <= 0;
			instr_and <= 0;
		end
	end
	localparam cpu_state_trap = 8'b10000000;
	localparam cpu_state_fetch = 8'b01000000;
	localparam cpu_state_ld_rs1 = 8'b00100000;
	localparam cpu_state_ld_rs2 = 8'b00010000;
	localparam cpu_state_exec = 8'b00001000;
	localparam cpu_state_shift = 8'b00000100;
	localparam cpu_state_stmem = 8'b00000010;
	localparam cpu_state_ldmem = 8'b00000001;
	reg [7:0] cpu_state;
	reg [1:0] irq_state;
	reg [127:0] dbg_ascii_state;
	always @(*) begin
		dbg_ascii_state = "";
		if (cpu_state == cpu_state_trap)
			dbg_ascii_state = "trap";
		if (cpu_state == cpu_state_fetch)
			dbg_ascii_state = "fetch";
		if (cpu_state == cpu_state_ld_rs1)
			dbg_ascii_state = "ld_rs1";
		if (cpu_state == cpu_state_ld_rs2)
			dbg_ascii_state = "ld_rs2";
		if (cpu_state == cpu_state_exec)
			dbg_ascii_state = "exec";
		if (cpu_state == cpu_state_shift)
			dbg_ascii_state = "shift";
		if (cpu_state == cpu_state_stmem)
			dbg_ascii_state = "stmem";
		if (cpu_state == cpu_state_ldmem)
			dbg_ascii_state = "ldmem";
	end
	reg set_mem_do_rinst;
	reg set_mem_do_rdata;
	reg set_mem_do_wdata;
	reg latched_store;
	reg latched_stalu;
	reg latched_branch;
	reg latched_compr;
	reg latched_trace;
	reg latched_is_lu;
	reg latched_is_lh;
	reg latched_is_lb;
	reg [regindex_bits - 1:0] latched_rd;
	reg [31:0] current_pc;
	assign next_pc = (latched_store && latched_branch ? reg_out & ~1 : reg_next_pc);
	reg [3:0] pcpi_timeout_counter;
	reg pcpi_timeout;
	reg [31:0] next_irq_pending;
	reg do_waitirq;
	reg [31:0] alu_out;
	reg [31:0] alu_out_q;
	reg alu_out_0;
	reg alu_out_0_q;
	reg alu_wait;
	reg alu_wait_2;
	reg [31:0] alu_add_sub;
	reg [31:0] alu_shl;
	reg [31:0] alu_shr;
	reg alu_eq;
	reg alu_ltu;
	reg alu_lts;
	generate
		if (TWO_CYCLE_ALU) begin : genblk3
			always @(posedge clk) begin
				alu_add_sub <= (instr_sub ? reg_op1 - reg_op2 : reg_op1 + reg_op2);
				alu_eq <= reg_op1 == reg_op2;
				alu_lts <= $signed(reg_op1) < $signed(reg_op2);
				alu_ltu <= reg_op1 < reg_op2;
				alu_shl <= reg_op1 << reg_op2[4:0];
				alu_shr <= $signed({(instr_sra || instr_srai ? reg_op1[31] : 1'b0), reg_op1}) >>> reg_op2[4:0];
			end
		end
		else begin : genblk3
			always @(*) begin
				alu_add_sub = (instr_sub ? reg_op1 - reg_op2 : reg_op1 + reg_op2);
				alu_eq = reg_op1 == reg_op2;
				alu_lts = $signed(reg_op1) < $signed(reg_op2);
				alu_ltu = reg_op1 < reg_op2;
				alu_shl = reg_op1 << reg_op2[4:0];
				alu_shr = $signed({(instr_sra || instr_srai ? reg_op1[31] : 1'b0), reg_op1}) >>> reg_op2[4:0];
			end
		end
	endgenerate
	always @(*) begin
		alu_out_0 = 'bx;
		(* parallel_case, full_case *)
		case (1'b1)
			instr_beq: alu_out_0 = alu_eq;
			instr_bne: alu_out_0 = !alu_eq;
			instr_bge: alu_out_0 = !alu_lts;
			instr_bgeu: alu_out_0 = !alu_ltu;
			is_slti_blt_slt && (!TWO_CYCLE_COMPARE || !{instr_beq, instr_bne, instr_bge, instr_bgeu}): alu_out_0 = alu_lts;
			is_sltiu_bltu_sltu && (!TWO_CYCLE_COMPARE || !{instr_beq, instr_bne, instr_bge, instr_bgeu}): alu_out_0 = alu_ltu;
		endcase
		alu_out = 'bx;
		(* parallel_case, full_case *)
		case (1'b1)
			is_lui_auipc_jal_jalr_addi_add_sub: alu_out = alu_add_sub;
			is_compare: alu_out = alu_out_0;
			instr_xori || instr_xor: alu_out = reg_op1 ^ reg_op2;
			instr_ori || instr_or: alu_out = reg_op1 | reg_op2;
			instr_andi || instr_and: alu_out = reg_op1 & reg_op2;
			BARREL_SHIFTER && (instr_sll || instr_slli): alu_out = alu_shl;
			BARREL_SHIFTER && (((instr_srl || instr_srli) || instr_sra) || instr_srai): alu_out = alu_shr;
		endcase
	end
	reg clear_prefetched_high_word_q;
	always @(posedge clk) clear_prefetched_high_word_q <= clear_prefetched_high_word;
	always @(*) begin
		clear_prefetched_high_word = clear_prefetched_high_word_q;
		if (!prefetched_high_word)
			clear_prefetched_high_word = 0;
		if ((latched_branch || irq_state) || !resetn)
			clear_prefetched_high_word = COMPRESSED_ISA;
	end
	reg cpuregs_write;
	reg [31:0] cpuregs_wrdata;
	reg [31:0] cpuregs_rs1;
	reg [31:0] cpuregs_rs2;
	reg [regindex_bits - 1:0] decoded_rs;
	always @(*) begin
		cpuregs_write = 0;
		cpuregs_wrdata = 'bx;
		if (cpu_state == cpu_state_fetch)
			(* parallel_case *)
			case (1'b1)
				latched_branch: begin
					cpuregs_wrdata = reg_pc + (latched_compr ? 2 : 4);
					cpuregs_write = 1;
				end
				latched_store && !latched_branch: begin
					cpuregs_wrdata = (latched_stalu ? alu_out_q : reg_out);
					cpuregs_write = 1;
				end
				ENABLE_IRQ && irq_state[0]: begin
					cpuregs_wrdata = reg_next_pc | latched_compr;
					cpuregs_write = 1;
				end
				ENABLE_IRQ && irq_state[1]: begin
					cpuregs_wrdata = irq_pending & ~irq_mask;
					cpuregs_write = 1;
				end
			endcase
	end
	always @(posedge clk)
		if ((resetn && cpuregs_write) && latched_rd)
			cpuregs[latched_rd] <= cpuregs_wrdata;
	always @(*) begin
		decoded_rs = 'bx;
		if (ENABLE_REGS_DUALPORT) begin
			cpuregs_rs1 = (decoded_rs1 ? cpuregs[decoded_rs1] : 0);
			cpuregs_rs2 = (decoded_rs2 ? cpuregs[decoded_rs2] : 0);
		end
		else begin
			decoded_rs = (cpu_state == cpu_state_ld_rs2 ? decoded_rs2 : decoded_rs1);
			cpuregs_rs1 = (decoded_rs ? cpuregs[decoded_rs] : 0);
			cpuregs_rs2 = cpuregs_rs1;
		end
	end
	assign launch_next_insn = ((cpu_state == cpu_state_fetch) && decoder_trigger) && (((!ENABLE_IRQ || irq_delay) || irq_active) || !(irq_pending & ~irq_mask));
	always @(posedge clk) begin
		trap <= 0;
		reg_sh <= 'bx;
		reg_out <= 'bx;
		set_mem_do_rinst = 0;
		set_mem_do_rdata = 0;
		set_mem_do_wdata = 0;
		alu_out_0_q <= alu_out_0;
		alu_out_q <= alu_out;
		alu_wait <= 0;
		alu_wait_2 <= 0;
		if (launch_next_insn) begin
			dbg_rs1val <= 'bx;
			dbg_rs2val <= 'bx;
			dbg_rs1val_valid <= 0;
			dbg_rs2val_valid <= 0;
		end
		if (WITH_PCPI && CATCH_ILLINSN) begin
			if ((resetn && pcpi_valid) && !pcpi_int_wait) begin
				if (pcpi_timeout_counter)
					pcpi_timeout_counter <= pcpi_timeout_counter - 1;
			end
			else
				pcpi_timeout_counter <= ~0;
			pcpi_timeout <= !pcpi_timeout_counter;
		end
		if (ENABLE_COUNTERS) begin
			count_cycle <= (resetn ? count_cycle + 1 : 0);
			if (!ENABLE_COUNTERS64)
				count_cycle[63:32] <= 0;
		end
		else begin
			count_cycle <= 'bx;
			count_instr <= 'bx;
		end
		next_irq_pending = (ENABLE_IRQ ? irq_pending & LATCHED_IRQ : 'bx);
		if ((ENABLE_IRQ && ENABLE_IRQ_TIMER) && timer)
			timer <= timer - 1;
		decoder_trigger <= mem_do_rinst && mem_done;
		decoder_trigger_q <= decoder_trigger;
		decoder_pseudo_trigger <= 0;
		decoder_pseudo_trigger_q <= decoder_pseudo_trigger;
		do_waitirq <= 0;
		trace_valid <= 0;
		if (!ENABLE_TRACE)
			trace_data <= 'bx;
		if (!resetn) begin
			reg_pc <= PROGADDR_RESET;
			reg_next_pc <= PROGADDR_RESET;
			if (ENABLE_COUNTERS)
				count_instr <= 0;
			latched_store <= 0;
			latched_stalu <= 0;
			latched_branch <= 0;
			latched_trace <= 0;
			latched_is_lu <= 0;
			latched_is_lh <= 0;
			latched_is_lb <= 0;
			pcpi_valid <= 0;
			pcpi_timeout <= 0;
			irq_active <= 0;
			irq_delay <= 0;
			irq_mask <= ~0;
			next_irq_pending = 0;
			irq_state <= 0;
			eoi <= 0;
			timer <= 0;
			if (~STACKADDR) begin
				latched_store <= 1;
				latched_rd <= 2;
				reg_out <= STACKADDR;
			end
			cpu_state <= cpu_state_fetch;
		end
		else
			(* parallel_case, full_case *)
			case (cpu_state)
				cpu_state_trap: trap <= 1;
				cpu_state_fetch: begin
					mem_do_rinst <= !decoder_trigger && !do_waitirq;
					mem_wordsize <= 0;
					current_pc = reg_next_pc;
					(* parallel_case *)
					case (1'b1)
						latched_branch: current_pc = (latched_store ? (latched_stalu ? alu_out_q : reg_out) & ~1 : reg_next_pc);
						latched_store && !latched_branch:
							;
						ENABLE_IRQ && irq_state[0]: begin
							current_pc = PROGADDR_IRQ;
							irq_active <= 1;
							mem_do_rinst <= 1;
						end
						ENABLE_IRQ && irq_state[1]: begin
							eoi <= irq_pending & ~irq_mask;
							next_irq_pending = next_irq_pending & irq_mask;
						end
					endcase
					if (ENABLE_TRACE && latched_trace) begin
						latched_trace <= 0;
						trace_valid <= 1;
						if (latched_branch)
							trace_data <= ((irq_active ? TRACE_IRQ : 0) | TRACE_BRANCH) | (current_pc & 32'hfffffffe);
						else
							trace_data <= (irq_active ? TRACE_IRQ : 0) | (latched_stalu ? alu_out_q : reg_out);
					end
					reg_pc <= current_pc;
					reg_next_pc <= current_pc;
					latched_store <= 0;
					latched_stalu <= 0;
					latched_branch <= 0;
					latched_is_lu <= 0;
					latched_is_lh <= 0;
					latched_is_lb <= 0;
					latched_rd <= decoded_rd;
					latched_compr <= compressed_instr;
					if (ENABLE_IRQ && ((((decoder_trigger && !irq_active) && !irq_delay) && |(irq_pending & ~irq_mask)) || irq_state)) begin
						irq_state <= (irq_state == 2'b00 ? 2'b01 : (irq_state == 2'b01 ? 2'b10 : 2'b00));
						latched_compr <= latched_compr;
						if (ENABLE_IRQ_QREGS)
							latched_rd <= irqregs_offset | irq_state[0];
						else
							latched_rd <= (irq_state[0] ? 4 : 3);
					end
					else if ((ENABLE_IRQ && (decoder_trigger || do_waitirq)) && instr_waitirq) begin
						if (irq_pending) begin
							latched_store <= 1;
							reg_out <= irq_pending;
							reg_next_pc <= current_pc + (compressed_instr ? 2 : 4);
							mem_do_rinst <= 1;
						end
						else
							do_waitirq <= 1;
					end
					else if (decoder_trigger) begin
						irq_delay <= irq_active;
						reg_next_pc <= current_pc + (compressed_instr ? 2 : 4);
						if (ENABLE_TRACE)
							latched_trace <= 1;
						if (ENABLE_COUNTERS) begin
							count_instr <= count_instr + 1;
							if (!ENABLE_COUNTERS64)
								count_instr[63:32] <= 0;
						end
						if (instr_jal) begin
							mem_do_rinst <= 1;
							reg_next_pc <= current_pc + decoded_imm_j;
							latched_branch <= 1;
						end
						else begin
							mem_do_rinst <= 0;
							mem_do_prefetch <= !instr_jalr && !instr_retirq;
							cpu_state <= cpu_state_ld_rs1;
						end
					end
				end
				cpu_state_ld_rs1: begin
					reg_op1 <= 'bx;
					reg_op2 <= 'bx;
					(* parallel_case *)
					case (1'b1)
						(CATCH_ILLINSN || WITH_PCPI) && instr_trap:
							if (WITH_PCPI) begin
								reg_op1 <= cpuregs_rs1;
								dbg_rs1val <= cpuregs_rs1;
								dbg_rs1val_valid <= 1;
								if (ENABLE_REGS_DUALPORT) begin
									pcpi_valid <= 1;
									reg_sh <= cpuregs_rs2;
									reg_op2 <= cpuregs_rs2;
									dbg_rs2val <= cpuregs_rs2;
									dbg_rs2val_valid <= 1;
									if (pcpi_int_ready) begin
										mem_do_rinst <= 1;
										pcpi_valid <= 0;
										reg_out <= pcpi_int_rd;
										latched_store <= pcpi_int_wr;
										cpu_state <= cpu_state_fetch;
									end
									else if (CATCH_ILLINSN && (pcpi_timeout || instr_ecall_ebreak)) begin
										pcpi_valid <= 0;
										if ((ENABLE_IRQ && !irq_mask[irq_ebreak]) && !irq_active) begin
											next_irq_pending[irq_ebreak] = 1;
											cpu_state <= cpu_state_fetch;
										end
										else
											cpu_state <= cpu_state_trap;
									end
								end
								else
									cpu_state <= cpu_state_ld_rs2;
							end
							else if ((ENABLE_IRQ && !irq_mask[irq_ebreak]) && !irq_active) begin
								next_irq_pending[irq_ebreak] = 1;
								cpu_state <= cpu_state_fetch;
							end
							else
								cpu_state <= cpu_state_trap;
						ENABLE_COUNTERS && is_rdcycle_rdcycleh_rdinstr_rdinstrh: begin
							(* parallel_case, full_case *)
							case (1'b1)
								instr_rdcycle: reg_out <= count_cycle[31:0];
								instr_rdcycleh && ENABLE_COUNTERS64: reg_out <= count_cycle[63:32];
								instr_rdinstr: reg_out <= count_instr[31:0];
								instr_rdinstrh && ENABLE_COUNTERS64: reg_out <= count_instr[63:32];
							endcase
							latched_store <= 1;
							cpu_state <= cpu_state_fetch;
						end
						is_lui_auipc_jal: begin
							reg_op1 <= (instr_lui ? 0 : reg_pc);
							reg_op2 <= decoded_imm;
							if (TWO_CYCLE_ALU)
								alu_wait <= 1;
							else
								mem_do_rinst <= mem_do_prefetch;
							cpu_state <= cpu_state_exec;
						end
						(ENABLE_IRQ && ENABLE_IRQ_QREGS) && instr_getq: begin
							reg_out <= cpuregs_rs1;
							dbg_rs1val <= cpuregs_rs1;
							dbg_rs1val_valid <= 1;
							latched_store <= 1;
							cpu_state <= cpu_state_fetch;
						end
						(ENABLE_IRQ && ENABLE_IRQ_QREGS) && instr_setq: begin
							reg_out <= cpuregs_rs1;
							dbg_rs1val <= cpuregs_rs1;
							dbg_rs1val_valid <= 1;
							latched_rd <= latched_rd | irqregs_offset;
							latched_store <= 1;
							cpu_state <= cpu_state_fetch;
						end
						ENABLE_IRQ && instr_retirq: begin
							eoi <= 0;
							irq_active <= 0;
							latched_branch <= 1;
							latched_store <= 1;
							reg_out <= (CATCH_MISALIGN ? cpuregs_rs1 & 32'hfffffffe : cpuregs_rs1);
							dbg_rs1val <= cpuregs_rs1;
							dbg_rs1val_valid <= 1;
							cpu_state <= cpu_state_fetch;
						end
						ENABLE_IRQ && instr_maskirq: begin
							latched_store <= 1;
							reg_out <= irq_mask;
							irq_mask <= cpuregs_rs1 | MASKED_IRQ;
							dbg_rs1val <= cpuregs_rs1;
							dbg_rs1val_valid <= 1;
							cpu_state <= cpu_state_fetch;
						end
						(ENABLE_IRQ && ENABLE_IRQ_TIMER) && instr_timer: begin
							latched_store <= 1;
							reg_out <= timer;
							timer <= cpuregs_rs1;
							dbg_rs1val <= cpuregs_rs1;
							dbg_rs1val_valid <= 1;
							cpu_state <= cpu_state_fetch;
						end
						is_lb_lh_lw_lbu_lhu && !instr_trap: begin
							reg_op1 <= cpuregs_rs1;
							dbg_rs1val <= cpuregs_rs1;
							dbg_rs1val_valid <= 1;
							cpu_state <= cpu_state_ldmem;
							mem_do_rinst <= 1;
						end
						is_slli_srli_srai && !BARREL_SHIFTER: begin
							reg_op1 <= cpuregs_rs1;
							dbg_rs1val <= cpuregs_rs1;
							dbg_rs1val_valid <= 1;
							reg_sh <= decoded_rs2;
							cpu_state <= cpu_state_shift;
						end
						is_jalr_addi_slti_sltiu_xori_ori_andi, is_slli_srli_srai && BARREL_SHIFTER: begin
							reg_op1 <= cpuregs_rs1;
							dbg_rs1val <= cpuregs_rs1;
							dbg_rs1val_valid <= 1;
							reg_op2 <= (is_slli_srli_srai && BARREL_SHIFTER ? decoded_rs2 : decoded_imm);
							if (TWO_CYCLE_ALU)
								alu_wait <= 1;
							else
								mem_do_rinst <= mem_do_prefetch;
							cpu_state <= cpu_state_exec;
						end
						default: begin
							reg_op1 <= cpuregs_rs1;
							dbg_rs1val <= cpuregs_rs1;
							dbg_rs1val_valid <= 1;
							if (ENABLE_REGS_DUALPORT) begin
								reg_sh <= cpuregs_rs2;
								reg_op2 <= cpuregs_rs2;
								dbg_rs2val <= cpuregs_rs2;
								dbg_rs2val_valid <= 1;
								(* parallel_case *)
								case (1'b1)
									is_sb_sh_sw: begin
										cpu_state <= cpu_state_stmem;
										mem_do_rinst <= 1;
									end
									is_sll_srl_sra && !BARREL_SHIFTER: cpu_state <= cpu_state_shift;
									default: begin
										if (TWO_CYCLE_ALU || (TWO_CYCLE_COMPARE && is_beq_bne_blt_bge_bltu_bgeu)) begin
											alu_wait_2 <= TWO_CYCLE_ALU && (TWO_CYCLE_COMPARE && is_beq_bne_blt_bge_bltu_bgeu);
											alu_wait <= 1;
										end
										else
											mem_do_rinst <= mem_do_prefetch;
										cpu_state <= cpu_state_exec;
									end
								endcase
							end
							else
								cpu_state <= cpu_state_ld_rs2;
						end
					endcase
				end
				cpu_state_ld_rs2: begin
					reg_sh <= cpuregs_rs2;
					reg_op2 <= cpuregs_rs2;
					dbg_rs2val <= cpuregs_rs2;
					dbg_rs2val_valid <= 1;
					(* parallel_case *)
					case (1'b1)
						WITH_PCPI && instr_trap: begin
							pcpi_valid <= 1;
							if (pcpi_int_ready) begin
								mem_do_rinst <= 1;
								pcpi_valid <= 0;
								reg_out <= pcpi_int_rd;
								latched_store <= pcpi_int_wr;
								cpu_state <= cpu_state_fetch;
							end
							else if (CATCH_ILLINSN && (pcpi_timeout || instr_ecall_ebreak)) begin
								pcpi_valid <= 0;
								if ((ENABLE_IRQ && !irq_mask[irq_ebreak]) && !irq_active) begin
									next_irq_pending[irq_ebreak] = 1;
									cpu_state <= cpu_state_fetch;
								end
								else
									cpu_state <= cpu_state_trap;
							end
						end
						is_sb_sh_sw: begin
							cpu_state <= cpu_state_stmem;
							mem_do_rinst <= 1;
						end
						is_sll_srl_sra && !BARREL_SHIFTER: cpu_state <= cpu_state_shift;
						default: begin
							if (TWO_CYCLE_ALU || (TWO_CYCLE_COMPARE && is_beq_bne_blt_bge_bltu_bgeu)) begin
								alu_wait_2 <= TWO_CYCLE_ALU && (TWO_CYCLE_COMPARE && is_beq_bne_blt_bge_bltu_bgeu);
								alu_wait <= 1;
							end
							else
								mem_do_rinst <= mem_do_prefetch;
							cpu_state <= cpu_state_exec;
						end
					endcase
				end
				cpu_state_exec: begin
					reg_out <= reg_pc + decoded_imm;
					if ((TWO_CYCLE_ALU || TWO_CYCLE_COMPARE) && (alu_wait || alu_wait_2)) begin
						mem_do_rinst <= mem_do_prefetch && !alu_wait_2;
						alu_wait <= alu_wait_2;
					end
					else if (is_beq_bne_blt_bge_bltu_bgeu) begin
						latched_rd <= 0;
						latched_store <= (TWO_CYCLE_COMPARE ? alu_out_0_q : alu_out_0);
						latched_branch <= (TWO_CYCLE_COMPARE ? alu_out_0_q : alu_out_0);
						if (mem_done)
							cpu_state <= cpu_state_fetch;
						if ((TWO_CYCLE_COMPARE ? alu_out_0_q : alu_out_0)) begin
							decoder_trigger <= 0;
							set_mem_do_rinst = 1;
						end
					end
					else begin
						latched_branch <= instr_jalr;
						latched_store <= 1;
						latched_stalu <= 1;
						cpu_state <= cpu_state_fetch;
					end
				end
				cpu_state_shift: begin
					latched_store <= 1;
					if (reg_sh == 0) begin
						reg_out <= reg_op1;
						mem_do_rinst <= mem_do_prefetch;
						cpu_state <= cpu_state_fetch;
					end
					else if (TWO_STAGE_SHIFT && (reg_sh >= 4)) begin
						(* parallel_case, full_case *)
						case (1'b1)
							instr_slli || instr_sll: reg_op1 <= reg_op1 << 4;
							instr_srli || instr_srl: reg_op1 <= reg_op1 >> 4;
							instr_srai || instr_sra: reg_op1 <= $signed(reg_op1) >>> 4;
						endcase
						reg_sh <= reg_sh - 4;
					end
					else begin
						(* parallel_case, full_case *)
						case (1'b1)
							instr_slli || instr_sll: reg_op1 <= reg_op1 << 1;
							instr_srli || instr_srl: reg_op1 <= reg_op1 >> 1;
							instr_srai || instr_sra: reg_op1 <= $signed(reg_op1) >>> 1;
						endcase
						reg_sh <= reg_sh - 1;
					end
				end
				cpu_state_stmem: begin
					if (ENABLE_TRACE)
						reg_out <= reg_op2;
					if (!mem_do_prefetch || mem_done) begin
						if (!mem_do_wdata) begin
							(* parallel_case, full_case *)
							case (1'b1)
								instr_sb: mem_wordsize <= 2;
								instr_sh: mem_wordsize <= 1;
								instr_sw: mem_wordsize <= 0;
							endcase
							if (ENABLE_TRACE) begin
								trace_valid <= 1;
								trace_data <= ((irq_active ? TRACE_IRQ : 0) | TRACE_ADDR) | ((reg_op1 + decoded_imm) & 32'hffffffff);
							end
							reg_op1 <= reg_op1 + decoded_imm;
							set_mem_do_wdata = 1;
						end
						if (!mem_do_prefetch && mem_done) begin
							cpu_state <= cpu_state_fetch;
							decoder_trigger <= 1;
							decoder_pseudo_trigger <= 1;
						end
					end
				end
				cpu_state_ldmem: begin
					latched_store <= 1;
					if (!mem_do_prefetch || mem_done) begin
						if (!mem_do_rdata) begin
							(* parallel_case, full_case *)
							case (1'b1)
								instr_lb || instr_lbu: mem_wordsize <= 2;
								instr_lh || instr_lhu: mem_wordsize <= 1;
								instr_lw: mem_wordsize <= 0;
							endcase
							latched_is_lu <= is_lbu_lhu_lw;
							latched_is_lh <= instr_lh;
							latched_is_lb <= instr_lb;
							if (ENABLE_TRACE) begin
								trace_valid <= 1;
								trace_data <= ((irq_active ? TRACE_IRQ : 0) | TRACE_ADDR) | ((reg_op1 + decoded_imm) & 32'hffffffff);
							end
							reg_op1 <= reg_op1 + decoded_imm;
							set_mem_do_rdata = 1;
						end
						if (!mem_do_prefetch && mem_done) begin
							(* parallel_case, full_case *)
							case (1'b1)
								latched_is_lu: reg_out <= mem_rdata_word;
								latched_is_lh: reg_out <= $signed(mem_rdata_word[15:0]);
								latched_is_lb: reg_out <= $signed(mem_rdata_word[7:0]);
							endcase
							decoder_trigger <= 1;
							decoder_pseudo_trigger <= 1;
							cpu_state <= cpu_state_fetch;
						end
					end
				end
			endcase
		if (ENABLE_IRQ) begin
			next_irq_pending = next_irq_pending | irq;
			if (ENABLE_IRQ_TIMER && timer) begin
				if ((timer - 1) == 0)
					next_irq_pending[irq_timer] = 1;
			end
		end
		if ((CATCH_MISALIGN && resetn) && (mem_do_rdata || mem_do_wdata)) begin
			if ((mem_wordsize == 0) && (reg_op1[1:0] != 0)) begin
				if ((ENABLE_IRQ && !irq_mask[irq_buserror]) && !irq_active)
					next_irq_pending[irq_buserror] = 1;
				else
					cpu_state <= cpu_state_trap;
			end
			if ((mem_wordsize == 1) && (reg_op1[0] != 0)) begin
				if ((ENABLE_IRQ && !irq_mask[irq_buserror]) && !irq_active)
					next_irq_pending[irq_buserror] = 1;
				else
					cpu_state <= cpu_state_trap;
			end
		end
		if (((CATCH_MISALIGN && resetn) && mem_do_rinst) && (COMPRESSED_ISA ? reg_pc[0] : |reg_pc[1:0])) begin
			if ((ENABLE_IRQ && !irq_mask[irq_buserror]) && !irq_active)
				next_irq_pending[irq_buserror] = 1;
			else
				cpu_state <= cpu_state_trap;
		end
		if (((!CATCH_ILLINSN && decoder_trigger_q) && !decoder_pseudo_trigger_q) && instr_ecall_ebreak)
			cpu_state <= cpu_state_trap;
		if (!resetn || mem_done) begin
			mem_do_prefetch <= 0;
			mem_do_rinst <= 0;
			mem_do_rdata <= 0;
			mem_do_wdata <= 0;
		end
		if (set_mem_do_rinst)
			mem_do_rinst <= 1;
		if (set_mem_do_rdata)
			mem_do_rdata <= 1;
		if (set_mem_do_wdata)
			mem_do_wdata <= 1;
		irq_pending <= next_irq_pending & ~MASKED_IRQ;
		if (!CATCH_MISALIGN) begin
			if (COMPRESSED_ISA) begin
				reg_pc[0] <= 0;
				reg_next_pc[0] <= 0;
			end
			else begin
				reg_pc[1:0] <= 0;
				reg_next_pc[1:0] <= 0;
			end
		end
		current_pc = 'bx;
	end
endmodule
module picorv32_regs (
	clk,
	wen,
	waddr,
	raddr1,
	raddr2,
	wdata,
	rdata1,
	rdata2
);
	input clk;
	input wen;
	input [5:0] waddr;
	input [5:0] raddr1;
	input [5:0] raddr2;
	input [31:0] wdata;
	output wire [31:0] rdata1;
	output wire [31:0] rdata2;
	reg [31:0] regs [0:30];
	always @(posedge clk)
		if (wen)
			regs[~waddr[4:0]] <= wdata;
	assign rdata1 = regs[~raddr1[4:0]];
	assign rdata2 = regs[~raddr2[4:0]];
endmodule
module picorv32_pcpi_mul (
	clk,
	resetn,
	pcpi_valid,
	pcpi_insn,
	pcpi_rs1,
	pcpi_rs2,
	pcpi_wr,
	pcpi_rd,
	pcpi_wait,
	pcpi_ready
);
	parameter STEPS_AT_ONCE = 1;
	parameter CARRY_CHAIN = 4;
	input clk;
	input resetn;
	input pcpi_valid;
	input [31:0] pcpi_insn;
	input [31:0] pcpi_rs1;
	input [31:0] pcpi_rs2;
	output reg pcpi_wr;
	output reg [31:0] pcpi_rd;
	output reg pcpi_wait;
	output reg pcpi_ready;
	reg instr_mul;
	reg instr_mulh;
	reg instr_mulhsu;
	reg instr_mulhu;
	wire instr_any_mul = |{instr_mul, instr_mulh, instr_mulhsu, instr_mulhu};
	wire instr_any_mulh = |{instr_mulh, instr_mulhsu, instr_mulhu};
	wire instr_rs1_signed = |{instr_mulh, instr_mulhsu};
	wire instr_rs2_signed = |{instr_mulh};
	reg pcpi_wait_q;
	wire mul_start = pcpi_wait && !pcpi_wait_q;
	always @(posedge clk) begin
		instr_mul <= 0;
		instr_mulh <= 0;
		instr_mulhsu <= 0;
		instr_mulhu <= 0;
		if (((resetn && pcpi_valid) && (pcpi_insn[6:0] == 7'b0110011)) && (pcpi_insn[31:25] == 7'b0000001))
			case (pcpi_insn[14:12])
				3'b000: instr_mul <= 1;
				3'b001: instr_mulh <= 1;
				3'b010: instr_mulhsu <= 1;
				3'b011: instr_mulhu <= 1;
			endcase
		pcpi_wait <= instr_any_mul;
		pcpi_wait_q <= pcpi_wait;
	end
	reg [63:0] rs1;
	reg [63:0] rs2;
	reg [63:0] rd;
	reg [63:0] rdx;
	reg [63:0] next_rs1;
	reg [63:0] next_rs2;
	reg [63:0] this_rs2;
	reg [63:0] next_rd;
	reg [63:0] next_rdx;
	reg [63:0] next_rdt;
	reg [6:0] mul_counter;
	reg mul_waiting;
	reg mul_finish;
	integer i;
	integer j;
	always @(*) begin
		next_rd = rd;
		next_rdx = rdx;
		next_rs1 = rs1;
		next_rs2 = rs2;
		for (i = 0; i < STEPS_AT_ONCE; i = i + 1)
			begin
				this_rs2 = (next_rs1[0] ? next_rs2 : 0);
				if (CARRY_CHAIN == 0) begin
					next_rdt = (next_rd ^ next_rdx) ^ this_rs2;
					next_rdx = (((next_rd & next_rdx) | (next_rd & this_rs2)) | (next_rdx & this_rs2)) << 1;
					next_rd = next_rdt;
				end
				else begin
					next_rdt = 0;
					for (j = 0; j < 64; j = j + CARRY_CHAIN)
						{next_rdt[(j + CARRY_CHAIN) - 1], next_rd[j+:CARRY_CHAIN]} = (next_rd[j+:CARRY_CHAIN] + next_rdx[j+:CARRY_CHAIN]) + this_rs2[j+:CARRY_CHAIN];
					next_rdx = next_rdt << 1;
				end
				next_rs1 = next_rs1 >> 1;
				next_rs2 = next_rs2 << 1;
			end
	end
	always @(posedge clk) begin
		mul_finish <= 0;
		if (!resetn)
			mul_waiting <= 1;
		else if (mul_waiting) begin
			if (instr_rs1_signed)
				rs1 <= $signed(pcpi_rs1);
			else
				rs1 <= $unsigned(pcpi_rs1);
			if (instr_rs2_signed)
				rs2 <= $signed(pcpi_rs2);
			else
				rs2 <= $unsigned(pcpi_rs2);
			rd <= 0;
			rdx <= 0;
			mul_counter <= (instr_any_mulh ? 63 - STEPS_AT_ONCE : 31 - STEPS_AT_ONCE);
			mul_waiting <= !mul_start;
		end
		else begin
			rd <= next_rd;
			rdx <= next_rdx;
			rs1 <= next_rs1;
			rs2 <= next_rs2;
			mul_counter <= mul_counter - STEPS_AT_ONCE;
			if (mul_counter[6]) begin
				mul_finish <= 1;
				mul_waiting <= 1;
			end
		end
	end
	always @(posedge clk) begin
		pcpi_wr <= 0;
		pcpi_ready <= 0;
		if (mul_finish && resetn) begin
			pcpi_wr <= 1;
			pcpi_ready <= 1;
			pcpi_rd <= (instr_any_mulh ? rd >> 32 : rd);
		end
	end
endmodule
module picorv32_pcpi_fast_mul (
	clk,
	resetn,
	pcpi_valid,
	pcpi_insn,
	pcpi_rs1,
	pcpi_rs2,
	pcpi_wr,
	pcpi_rd,
	pcpi_wait,
	pcpi_ready
);
	parameter EXTRA_MUL_FFS = 0;
	parameter EXTRA_INSN_FFS = 0;
	parameter MUL_CLKGATE = 0;
	input clk;
	input resetn;
	input pcpi_valid;
	input [31:0] pcpi_insn;
	input [31:0] pcpi_rs1;
	input [31:0] pcpi_rs2;
	output wire pcpi_wr;
	output wire [31:0] pcpi_rd;
	output wire pcpi_wait;
	output wire pcpi_ready;
	reg instr_mul;
	reg instr_mulh;
	reg instr_mulhsu;
	reg instr_mulhu;
	wire instr_any_mul = |{instr_mul, instr_mulh, instr_mulhsu, instr_mulhu};
	wire instr_any_mulh = |{instr_mulh, instr_mulhsu, instr_mulhu};
	wire instr_rs1_signed = |{instr_mulh, instr_mulhsu};
	wire instr_rs2_signed = |{instr_mulh};
	reg shift_out;
	reg [3:0] active;
	reg [32:0] rs1;
	reg [32:0] rs2;
	reg [32:0] rs1_q;
	reg [32:0] rs2_q;
	reg [63:0] rd;
	reg [63:0] rd_q;
	wire pcpi_insn_valid = (pcpi_valid && (pcpi_insn[6:0] == 7'b0110011)) && (pcpi_insn[31:25] == 7'b0000001);
	reg pcpi_insn_valid_q;
	always @(*) begin
		instr_mul = 0;
		instr_mulh = 0;
		instr_mulhsu = 0;
		instr_mulhu = 0;
		if (resetn && (EXTRA_INSN_FFS ? pcpi_insn_valid_q : pcpi_insn_valid))
			case (pcpi_insn[14:12])
				3'b000: instr_mul = 1;
				3'b001: instr_mulh = 1;
				3'b010: instr_mulhsu = 1;
				3'b011: instr_mulhu = 1;
			endcase
	end
	always @(posedge clk) begin
		pcpi_insn_valid_q <= pcpi_insn_valid;
		if (!MUL_CLKGATE || active[0]) begin
			rs1_q <= rs1;
			rs2_q <= rs2;
		end
		if (!MUL_CLKGATE || active[1])
			rd <= $signed((EXTRA_MUL_FFS ? rs1_q : rs1)) * $signed((EXTRA_MUL_FFS ? rs2_q : rs2));
		if (!MUL_CLKGATE || active[2])
			rd_q <= rd;
	end
	always @(posedge clk) begin
		if (instr_any_mul && !(EXTRA_MUL_FFS ? active[3:0] : active[1:0])) begin
			if (instr_rs1_signed)
				rs1 <= $signed(pcpi_rs1);
			else
				rs1 <= $unsigned(pcpi_rs1);
			if (instr_rs2_signed)
				rs2 <= $signed(pcpi_rs2);
			else
				rs2 <= $unsigned(pcpi_rs2);
			active[0] <= 1;
		end
		else
			active[0] <= 0;
		active[3:1] <= active;
		shift_out <= instr_any_mulh;
		if (!resetn)
			active <= 0;
	end
	assign pcpi_wr = active[(EXTRA_MUL_FFS ? 3 : 1)];
	assign pcpi_wait = 0;
	assign pcpi_ready = active[(EXTRA_MUL_FFS ? 3 : 1)];
	assign pcpi_rd = (shift_out ? (EXTRA_MUL_FFS ? rd_q : rd) >> 32 : (EXTRA_MUL_FFS ? rd_q : rd));
endmodule
module picorv32_pcpi_div (
	clk,
	resetn,
	pcpi_valid,
	pcpi_insn,
	pcpi_rs1,
	pcpi_rs2,
	pcpi_wr,
	pcpi_rd,
	pcpi_wait,
	pcpi_ready
);
	input clk;
	input resetn;
	input pcpi_valid;
	input [31:0] pcpi_insn;
	input [31:0] pcpi_rs1;
	input [31:0] pcpi_rs2;
	output reg pcpi_wr;
	output reg [31:0] pcpi_rd;
	output reg pcpi_wait;
	output reg pcpi_ready;
	reg instr_div;
	reg instr_divu;
	reg instr_rem;
	reg instr_remu;
	wire instr_any_div_rem = |{instr_div, instr_divu, instr_rem, instr_remu};
	reg pcpi_wait_q;
	wire start = pcpi_wait && !pcpi_wait_q;
	always @(posedge clk) begin
		instr_div <= 0;
		instr_divu <= 0;
		instr_rem <= 0;
		instr_remu <= 0;
		if ((((resetn && pcpi_valid) && !pcpi_ready) && (pcpi_insn[6:0] == 7'b0110011)) && (pcpi_insn[31:25] == 7'b0000001))
			case (pcpi_insn[14:12])
				3'b100: instr_div <= 1;
				3'b101: instr_divu <= 1;
				3'b110: instr_rem <= 1;
				3'b111: instr_remu <= 1;
			endcase
		pcpi_wait <= instr_any_div_rem && resetn;
		pcpi_wait_q <= pcpi_wait && resetn;
	end
	reg [31:0] dividend;
	reg [62:0] divisor;
	reg [31:0] quotient;
	reg [31:0] quotient_msk;
	reg running;
	reg outsign;
	always @(posedge clk) begin
		pcpi_ready <= 0;
		pcpi_wr <= 0;
		pcpi_rd <= 'bx;
		if (!resetn)
			running <= 0;
		else if (start) begin
			running <= 1;
			dividend <= ((instr_div || instr_rem) && pcpi_rs1[31] ? -pcpi_rs1 : pcpi_rs1);
			divisor <= ((instr_div || instr_rem) && pcpi_rs2[31] ? -pcpi_rs2 : pcpi_rs2) << 31;
			outsign <= ((instr_div && (pcpi_rs1[31] != pcpi_rs2[31])) && |pcpi_rs2) || (instr_rem && pcpi_rs1[31]);
			quotient <= 0;
			quotient_msk <= 33'sd2147483648;
		end
		else if (!quotient_msk && running) begin
			running <= 0;
			pcpi_ready <= 1;
			pcpi_wr <= 1;
			if (instr_div || instr_divu)
				pcpi_rd <= (outsign ? -quotient : quotient);
			else
				pcpi_rd <= (outsign ? -dividend : dividend);
		end
		else begin
			if (divisor <= dividend) begin
				dividend <= dividend - divisor;
				quotient <= quotient | quotient_msk;
			end
			divisor <= divisor >> 1;
			quotient_msk <= quotient_msk >> 1;
		end
	end
endmodule
module picorv32_axi (
	clk,
	resetn,
	trap,
	mem_axi_awvalid,
	mem_axi_awready,
	mem_axi_awaddr,
	mem_axi_awprot,
	mem_axi_wvalid,
	mem_axi_wready,
	mem_axi_wdata,
	mem_axi_wstrb,
	mem_axi_bvalid,
	mem_axi_bready,
	mem_axi_arvalid,
	mem_axi_arready,
	mem_axi_araddr,
	mem_axi_arprot,
	mem_axi_rvalid,
	mem_axi_rready,
	mem_axi_rdata,
	pcpi_valid,
	pcpi_insn,
	pcpi_rs1,
	pcpi_rs2,
	pcpi_wr,
	pcpi_rd,
	pcpi_wait,
	pcpi_ready,
	irq,
	eoi,
	trace_valid,
	trace_data
);
	parameter [0:0] ENABLE_COUNTERS = 1;
	parameter [0:0] ENABLE_COUNTERS64 = 1;
	parameter [0:0] ENABLE_REGS_16_31 = 1;
	parameter [0:0] ENABLE_REGS_DUALPORT = 1;
	parameter [0:0] TWO_STAGE_SHIFT = 1;
	parameter [0:0] BARREL_SHIFTER = 0;
	parameter [0:0] TWO_CYCLE_COMPARE = 0;
	parameter [0:0] TWO_CYCLE_ALU = 0;
	parameter [0:0] COMPRESSED_ISA = 0;
	parameter [0:0] CATCH_MISALIGN = 1;
	parameter [0:0] CATCH_ILLINSN = 1;
	parameter [0:0] ENABLE_PCPI = 0;
	parameter [0:0] ENABLE_MUL = 0;
	parameter [0:0] ENABLE_FAST_MUL = 0;
	parameter [0:0] ENABLE_DIV = 0;
	parameter [0:0] ENABLE_IRQ = 0;
	parameter [0:0] ENABLE_IRQ_QREGS = 1;
	parameter [0:0] ENABLE_IRQ_TIMER = 1;
	parameter [0:0] ENABLE_TRACE = 0;
	parameter [0:0] REGS_INIT_ZERO = 0;
	parameter [31:0] MASKED_IRQ = 32'h00000000;
	parameter [31:0] LATCHED_IRQ = 32'hffffffff;
	parameter [31:0] PROGADDR_RESET = 32'h00000000;
	parameter [31:0] PROGADDR_IRQ = 32'h00000010;
	parameter [31:0] STACKADDR = 32'hffffffff;
	input clk;
	input resetn;
	output wire trap;
	output wire mem_axi_awvalid;
	input mem_axi_awready;
	output wire [31:0] mem_axi_awaddr;
	output wire [2:0] mem_axi_awprot;
	output wire mem_axi_wvalid;
	input mem_axi_wready;
	output wire [31:0] mem_axi_wdata;
	output wire [3:0] mem_axi_wstrb;
	input mem_axi_bvalid;
	output wire mem_axi_bready;
	output wire mem_axi_arvalid;
	input mem_axi_arready;
	output wire [31:0] mem_axi_araddr;
	output wire [2:0] mem_axi_arprot;
	input mem_axi_rvalid;
	output wire mem_axi_rready;
	input [31:0] mem_axi_rdata;
	output wire pcpi_valid;
	output wire [31:0] pcpi_insn;
	output wire [31:0] pcpi_rs1;
	output wire [31:0] pcpi_rs2;
	input pcpi_wr;
	input [31:0] pcpi_rd;
	input pcpi_wait;
	input pcpi_ready;
	input [31:0] irq;
	output wire [31:0] eoi;
	output wire trace_valid;
	output wire [35:0] trace_data;
	wire mem_valid;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0] mem_wstrb;
	wire mem_instr;
	wire mem_ready;
	wire [31:0] mem_rdata;
	picorv32_axi_adapter axi_adapter(
		.clk(clk),
		.resetn(resetn),
		.mem_axi_awvalid(mem_axi_awvalid),
		.mem_axi_awready(mem_axi_awready),
		.mem_axi_awaddr(mem_axi_awaddr),
		.mem_axi_awprot(mem_axi_awprot),
		.mem_axi_wvalid(mem_axi_wvalid),
		.mem_axi_wready(mem_axi_wready),
		.mem_axi_wdata(mem_axi_wdata),
		.mem_axi_wstrb(mem_axi_wstrb),
		.mem_axi_bvalid(mem_axi_bvalid),
		.mem_axi_bready(mem_axi_bready),
		.mem_axi_arvalid(mem_axi_arvalid),
		.mem_axi_arready(mem_axi_arready),
		.mem_axi_araddr(mem_axi_araddr),
		.mem_axi_arprot(mem_axi_arprot),
		.mem_axi_rvalid(mem_axi_rvalid),
		.mem_axi_rready(mem_axi_rready),
		.mem_axi_rdata(mem_axi_rdata),
		.mem_valid(mem_valid),
		.mem_instr(mem_instr),
		.mem_ready(mem_ready),
		.mem_addr(mem_addr),
		.mem_wdata(mem_wdata),
		.mem_wstrb(mem_wstrb),
		.mem_rdata(mem_rdata)
	);
	picorv32 #(
		.ENABLE_COUNTERS(ENABLE_COUNTERS),
		.ENABLE_COUNTERS64(ENABLE_COUNTERS64),
		.ENABLE_REGS_16_31(ENABLE_REGS_16_31),
		.ENABLE_REGS_DUALPORT(ENABLE_REGS_DUALPORT),
		.TWO_STAGE_SHIFT(TWO_STAGE_SHIFT),
		.BARREL_SHIFTER(BARREL_SHIFTER),
		.TWO_CYCLE_COMPARE(TWO_CYCLE_COMPARE),
		.TWO_CYCLE_ALU(TWO_CYCLE_ALU),
		.COMPRESSED_ISA(COMPRESSED_ISA),
		.CATCH_MISALIGN(CATCH_MISALIGN),
		.CATCH_ILLINSN(CATCH_ILLINSN),
		.ENABLE_PCPI(ENABLE_PCPI),
		.ENABLE_MUL(ENABLE_MUL),
		.ENABLE_FAST_MUL(ENABLE_FAST_MUL),
		.ENABLE_DIV(ENABLE_DIV),
		.ENABLE_IRQ(ENABLE_IRQ),
		.ENABLE_IRQ_QREGS(ENABLE_IRQ_QREGS),
		.ENABLE_IRQ_TIMER(ENABLE_IRQ_TIMER),
		.ENABLE_TRACE(ENABLE_TRACE),
		.REGS_INIT_ZERO(REGS_INIT_ZERO),
		.MASKED_IRQ(MASKED_IRQ),
		.LATCHED_IRQ(LATCHED_IRQ),
		.PROGADDR_RESET(PROGADDR_RESET),
		.PROGADDR_IRQ(PROGADDR_IRQ),
		.STACKADDR(STACKADDR)
	) picorv32_core(
		.clk(clk),
		.resetn(resetn),
		.trap(trap),
		.mem_valid(mem_valid),
		.mem_addr(mem_addr),
		.mem_wdata(mem_wdata),
		.mem_wstrb(mem_wstrb),
		.mem_instr(mem_instr),
		.mem_ready(mem_ready),
		.mem_rdata(mem_rdata),
		.pcpi_valid(pcpi_valid),
		.pcpi_insn(pcpi_insn),
		.pcpi_rs1(pcpi_rs1),
		.pcpi_rs2(pcpi_rs2),
		.pcpi_wr(pcpi_wr),
		.pcpi_rd(pcpi_rd),
		.pcpi_wait(pcpi_wait),
		.pcpi_ready(pcpi_ready),
		.irq(irq),
		.eoi(eoi),
		.trace_valid(trace_valid),
		.trace_data(trace_data)
	);
endmodule
module picorv32_axi_adapter (
	clk,
	resetn,
	mem_axi_awvalid,
	mem_axi_awready,
	mem_axi_awaddr,
	mem_axi_awprot,
	mem_axi_wvalid,
	mem_axi_wready,
	mem_axi_wdata,
	mem_axi_wstrb,
	mem_axi_bvalid,
	mem_axi_bready,
	mem_axi_arvalid,
	mem_axi_arready,
	mem_axi_araddr,
	mem_axi_arprot,
	mem_axi_rvalid,
	mem_axi_rready,
	mem_axi_rdata,
	mem_valid,
	mem_instr,
	mem_ready,
	mem_addr,
	mem_wdata,
	mem_wstrb,
	mem_rdata
);
	input clk;
	input resetn;
	output wire mem_axi_awvalid;
	input mem_axi_awready;
	output wire [31:0] mem_axi_awaddr;
	output wire [2:0] mem_axi_awprot;
	output wire mem_axi_wvalid;
	input mem_axi_wready;
	output wire [31:0] mem_axi_wdata;
	output wire [3:0] mem_axi_wstrb;
	input mem_axi_bvalid;
	output wire mem_axi_bready;
	output wire mem_axi_arvalid;
	input mem_axi_arready;
	output wire [31:0] mem_axi_araddr;
	output wire [2:0] mem_axi_arprot;
	input mem_axi_rvalid;
	output wire mem_axi_rready;
	input [31:0] mem_axi_rdata;
	input mem_valid;
	input mem_instr;
	output wire mem_ready;
	input [31:0] mem_addr;
	input [31:0] mem_wdata;
	input [3:0] mem_wstrb;
	output wire [31:0] mem_rdata;
	reg ack_awvalid;
	reg ack_arvalid;
	reg ack_wvalid;
	reg xfer_done;
	assign mem_axi_awvalid = (mem_valid && |mem_wstrb) && !ack_awvalid;
	assign mem_axi_awaddr = mem_addr;
	assign mem_axi_awprot = 0;
	assign mem_axi_arvalid = (mem_valid && !mem_wstrb) && !ack_arvalid;
	assign mem_axi_araddr = mem_addr;
	assign mem_axi_arprot = (mem_instr ? 3'b100 : 3'b000);
	assign mem_axi_wvalid = (mem_valid && |mem_wstrb) && !ack_wvalid;
	assign mem_axi_wdata = mem_wdata;
	assign mem_axi_wstrb = mem_wstrb;
	assign mem_ready = mem_axi_bvalid || mem_axi_rvalid;
	assign mem_axi_bready = mem_valid && |mem_wstrb;
	assign mem_axi_rready = mem_valid && !mem_wstrb;
	assign mem_rdata = mem_axi_rdata;
	always @(posedge clk)
		if (!resetn)
			ack_awvalid <= 0;
		else begin
			xfer_done <= mem_valid && mem_ready;
			if (mem_axi_awready && mem_axi_awvalid)
				ack_awvalid <= 1;
			if (mem_axi_arready && mem_axi_arvalid)
				ack_arvalid <= 1;
			if (mem_axi_wready && mem_axi_wvalid)
				ack_wvalid <= 1;
			if (xfer_done || !mem_valid) begin
				ack_awvalid <= 0;
				ack_arvalid <= 0;
				ack_wvalid <= 0;
			end
		end
endmodule
module picorv32_wb (
	trap,
	wb_rst_i,
	wb_clk_i,
	wbm_adr_o,
	wbm_dat_o,
	wbm_dat_i,
	wbm_we_o,
	wbm_sel_o,
	wbm_stb_o,
	wbm_ack_i,
	wbm_cyc_o,
	pcpi_valid,
	pcpi_insn,
	pcpi_rs1,
	pcpi_rs2,
	pcpi_wr,
	pcpi_rd,
	pcpi_wait,
	pcpi_ready,
	irq,
	eoi,
	trace_valid,
	trace_data,
	mem_instr
);
	parameter [0:0] ENABLE_COUNTERS = 1;
	parameter [0:0] ENABLE_COUNTERS64 = 1;
	parameter [0:0] ENABLE_REGS_16_31 = 1;
	parameter [0:0] ENABLE_REGS_DUALPORT = 1;
	parameter [0:0] TWO_STAGE_SHIFT = 1;
	parameter [0:0] BARREL_SHIFTER = 0;
	parameter [0:0] TWO_CYCLE_COMPARE = 0;
	parameter [0:0] TWO_CYCLE_ALU = 0;
	parameter [0:0] COMPRESSED_ISA = 0;
	parameter [0:0] CATCH_MISALIGN = 1;
	parameter [0:0] CATCH_ILLINSN = 1;
	parameter [0:0] ENABLE_PCPI = 0;
	parameter [0:0] ENABLE_MUL = 0;
	parameter [0:0] ENABLE_FAST_MUL = 0;
	parameter [0:0] ENABLE_DIV = 0;
	parameter [0:0] ENABLE_IRQ = 0;
	parameter [0:0] ENABLE_IRQ_QREGS = 1;
	parameter [0:0] ENABLE_IRQ_TIMER = 1;
	parameter [0:0] ENABLE_TRACE = 0;
	parameter [0:0] REGS_INIT_ZERO = 0;
	parameter [31:0] MASKED_IRQ = 32'h00000000;
	parameter [31:0] LATCHED_IRQ = 32'hffffffff;
	parameter [31:0] PROGADDR_RESET = 32'h00000000;
	parameter [31:0] PROGADDR_IRQ = 32'h00000010;
	parameter [31:0] STACKADDR = 32'hffffffff;
	output wire trap;
	input wb_rst_i;
	input wb_clk_i;
	output reg [31:0] wbm_adr_o;
	output reg [31:0] wbm_dat_o;
	input [31:0] wbm_dat_i;
	output reg wbm_we_o;
	output reg [3:0] wbm_sel_o;
	output reg wbm_stb_o;
	input wbm_ack_i;
	output reg wbm_cyc_o;
	output wire pcpi_valid;
	output wire [31:0] pcpi_insn;
	output wire [31:0] pcpi_rs1;
	output wire [31:0] pcpi_rs2;
	input pcpi_wr;
	input [31:0] pcpi_rd;
	input pcpi_wait;
	input pcpi_ready;
	input [31:0] irq;
	output wire [31:0] eoi;
	output wire trace_valid;
	output wire [35:0] trace_data;
	output wire mem_instr;
	wire mem_valid;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0] mem_wstrb;
	reg mem_ready;
	reg [31:0] mem_rdata;
	wire clk;
	wire resetn;
	assign clk = wb_clk_i;
	assign resetn = ~wb_rst_i;
	picorv32 #(
		.ENABLE_COUNTERS(ENABLE_COUNTERS),
		.ENABLE_COUNTERS64(ENABLE_COUNTERS64),
		.ENABLE_REGS_16_31(ENABLE_REGS_16_31),
		.ENABLE_REGS_DUALPORT(ENABLE_REGS_DUALPORT),
		.TWO_STAGE_SHIFT(TWO_STAGE_SHIFT),
		.BARREL_SHIFTER(BARREL_SHIFTER),
		.TWO_CYCLE_COMPARE(TWO_CYCLE_COMPARE),
		.TWO_CYCLE_ALU(TWO_CYCLE_ALU),
		.COMPRESSED_ISA(COMPRESSED_ISA),
		.CATCH_MISALIGN(CATCH_MISALIGN),
		.CATCH_ILLINSN(CATCH_ILLINSN),
		.ENABLE_PCPI(ENABLE_PCPI),
		.ENABLE_MUL(ENABLE_MUL),
		.ENABLE_FAST_MUL(ENABLE_FAST_MUL),
		.ENABLE_DIV(ENABLE_DIV),
		.ENABLE_IRQ(ENABLE_IRQ),
		.ENABLE_IRQ_QREGS(ENABLE_IRQ_QREGS),
		.ENABLE_IRQ_TIMER(ENABLE_IRQ_TIMER),
		.ENABLE_TRACE(ENABLE_TRACE),
		.REGS_INIT_ZERO(REGS_INIT_ZERO),
		.MASKED_IRQ(MASKED_IRQ),
		.LATCHED_IRQ(LATCHED_IRQ),
		.PROGADDR_RESET(PROGADDR_RESET),
		.PROGADDR_IRQ(PROGADDR_IRQ),
		.STACKADDR(STACKADDR)
	) picorv32_core(
		.clk(clk),
		.resetn(resetn),
		.trap(trap),
		.mem_valid(mem_valid),
		.mem_addr(mem_addr),
		.mem_wdata(mem_wdata),
		.mem_wstrb(mem_wstrb),
		.mem_instr(mem_instr),
		.mem_ready(mem_ready),
		.mem_rdata(mem_rdata),
		.pcpi_valid(pcpi_valid),
		.pcpi_insn(pcpi_insn),
		.pcpi_rs1(pcpi_rs1),
		.pcpi_rs2(pcpi_rs2),
		.pcpi_wr(pcpi_wr),
		.pcpi_rd(pcpi_rd),
		.pcpi_wait(pcpi_wait),
		.pcpi_ready(pcpi_ready),
		.irq(irq),
		.eoi(eoi),
		.trace_valid(trace_valid),
		.trace_data(trace_data)
	);
	localparam IDLE = 2'b00;
	localparam WBSTART = 2'b01;
	localparam WBEND = 2'b10;
	reg [1:0] state;
	wire we;
	assign we = ((mem_wstrb[0] | mem_wstrb[1]) | mem_wstrb[2]) | mem_wstrb[3];
	always @(posedge wb_clk_i)
		if (wb_rst_i) begin
			wbm_adr_o <= 0;
			wbm_dat_o <= 0;
			wbm_we_o <= 0;
			wbm_sel_o <= 0;
			wbm_stb_o <= 0;
			wbm_cyc_o <= 0;
			state <= IDLE;
		end
		else
			case (state)
				IDLE:
					if (mem_valid) begin
						wbm_adr_o <= mem_addr;
						wbm_dat_o <= mem_wdata;
						wbm_we_o <= we;
						wbm_sel_o <= mem_wstrb;
						wbm_stb_o <= 1'b1;
						wbm_cyc_o <= 1'b1;
						state <= WBSTART;
					end
					else begin
						mem_ready <= 1'b0;
						wbm_stb_o <= 1'b0;
						wbm_cyc_o <= 1'b0;
						wbm_we_o <= 1'b0;
					end
				WBSTART:
					if (wbm_ack_i) begin
						mem_rdata <= wbm_dat_i;
						mem_ready <= 1'b1;
						state <= WBEND;
						wbm_stb_o <= 1'b0;
						wbm_cyc_o <= 1'b0;
						wbm_we_o <= 1'b0;
					end
				WBEND: begin
					mem_ready <= 1'b0;
					state <= IDLE;
				end
				default: state <= IDLE;
			endcase
endmodule
module uart (
	clk,
	resetn,
	ser_tx,
	ser_rx,
	ser_cts,
	ser_rts,
	mem_valid,
	mem_addr,
	mem_wdata,
	mem_wstrb,
	uart_ready,
	uart_sel,
	uart_rdata
);
	parameter [31:0] ADDR = 32'hffffffff;
	input clk;
	input resetn;
	output wire ser_tx;
	input ser_rx;
	input ser_cts;
	output wire ser_rts;
	input mem_valid;
	input [31:0] mem_addr;
	input [31:0] mem_wdata;
	input [3:0] mem_wstrb;
	output wire uart_ready;
	output wire uart_sel;
	output wire [31:0] uart_rdata;
	wire reg_div_sel = mem_valid && (mem_addr == ADDR);
	wire [31:0] reg_div_do;
	wire reg_dat_sel = mem_valid && (mem_addr == (ADDR + 4));
	wire [31:0] reg_dat_do;
	wire reg_dat_wait;
	wire reg_cts_sel = mem_valid && (mem_addr == (ADDR + 8));
	wire [31:0] reg_cts_do = {31'h00000000, ser_cts};
	wire reg_status_sel = mem_valid && (mem_addr == (ADDR + 12));
	wire reg_send_busy;
	wire [31:0] reg_status_do = {31'h00000000, reg_send_busy};
	assign uart_ready = ((reg_div_sel || reg_cts_sel) || (reg_dat_sel && !reg_dat_wait)) || reg_status_sel;
	assign uart_sel = ((reg_div_sel || reg_cts_sel) || reg_dat_sel) || reg_status_sel;
	assign uart_rdata = (reg_div_sel ? reg_div_do : (reg_dat_sel ? reg_dat_do : (reg_cts_sel ? reg_cts_do : (reg_status_sel ? reg_status_do : 32'h00000000))));
	simpleuart simpleuart(
		.clk(clk),
		.resetn(resetn),
		.ser_tx(ser_tx),
		.ser_rx(ser_rx),
		.ser_rts(ser_rts),
		.reg_div_we((reg_div_sel ? mem_wstrb : 4'b0000)),
		.reg_div_di(mem_wdata),
		.reg_div_do(reg_div_do),
		.reg_dat_we((reg_dat_sel ? mem_wstrb[0] : 1'b0)),
		.reg_dat_re(reg_dat_sel && !(|mem_wstrb)),
		.reg_dat_di(mem_wdata),
		.reg_dat_do(reg_dat_do),
		.reg_dat_wait(reg_dat_wait),
		.reg_send_busy(reg_send_busy)
	);
endmodule
