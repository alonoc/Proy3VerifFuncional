`ifndef COVERGROUP_SDRC_SV
`define COVERGROUP_SDRC_SV

`include "sdrc_intf.sv"

class covergroups_sdram_ctrl;
	
	virtual sdrc_if sdram_ctrl_intf;
	
	covergroup wb_banks @(posedge sdram_ctrl_intf.sys_clk);
	
	`ifdef SDR_08COL_BITS
		column	:	coverpoint sdram_ctrl_intf.wb_addr_i[7:0];
		row		:  	coverpoint sdram_ctrl_intf.wb_addr_i[21:10];
        bank	:	coverpoint sdram_ctrl_intf.wb_addr_i[9:8]
	`elsif SDR_09COL_BITS
		column	:	coverpoint sdram_ctrl_intf.wb_addr_i[8:0];
		row		:  	coverpoint sdram_ctrl_intf.wb_addr_i[22:11];
		bank	:	coverpoint sdram_ctrl_intf.wb_addr_i[10:9]
	`elsif SDR_10COL_BITS
		column	:	coverpoint sdram_ctrl_intf.wb_addr_i[9:0];
		row		:  	coverpoint sdram_ctrl_intf.wb_addr_i[23:12];
		bank	:	coverpoint sdram_ctrl_intf.wb_addr_i[11:10]
	`else
		column	:	coverpoint sdram_ctrl_intf.wb_addr_i[10:0];
		row		:  	coverpoint sdram_ctrl_intf.wb_addr_i[24:13];
		bank	:	coverpoint sdram_ctrl_intf.wb_addr_i[12:11]
	`endif
		{
			bins bank_0	= {0};
			bins bank_1	= {1};
			bins bank_2	= {2};
			bins bank_3	= {3};
		}
		
		cmd		:	coverpoint {sdram_ctrl_intf.wb_we_i, sdram_ctrl_intf.wb_stb_i, sdram_ctrl_intf.wb_cyc_i}
		{
			bins cmd_rd = {3'b011};
			bins cmd_wr = {3'b111};
		}
		
		cmd_x_bank : cross cmd, bank;
		cmd_x_row_x_column_x_bank	: cross cmd, row, column, bank;
	endgroup
	
	covergroup sdram_banks @(posedge sdram_ctrl_intf.sdram_clk);
		bank	:	coverpoint sdram_ctrl_intf.sdr_ba
		{
			bins bank_0 = {0};
			bins bank_1 = {1};
			bins bank_2 = {2};
			bins bank_3 = {3};
		}
		
		cmd		: 	coverpoint {sdram_ctrl_intf.sdr_cs_n, sdram_ctrl_intf.sdr_ras_n,sdram_ctrl_intf.sdr_cas_n,sdram_ctrl_intf.sdr_we_n}
		{
			bins cmd_rd = {4'b0101};
			bins cmd_wr = {4'b0100};
		}
		
		cmd_x_bank : cross cmd, bank;
		
	endgroup
	
	function new(virtual sdrc_if sdram_ctrl_intf);
		this.sdram_ctrl_intf = sdram_ctrl_intf;
		
		// Cover points for test all banks
		this.wb_banks = new();
		this.sdram_banks = new();
	endfunction
	
 endclass

`endif