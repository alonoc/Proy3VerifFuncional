`ifndef COVERGROUP_SDRC_SV
`define COVERGROUP_SDRC_SV

`include "sdrc_intf.sv"

class covergroups_sdram_ctrl;
	
	virtual sdrc_if sdram_ctrl_intf;
	
	covergroup wish_bone_cg @(posedge sdram_ctrl_intf.sys_clk);
		
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
		
		cmd	: coverpoint {sdram_ctrl_intf.wb_we_i, sdram_ctrl_intf.wb_stb_i, sdram_ctrl_intf.wb_cyc_i}
		{
			bins cmd_rd = {3'b011};
			bins cmd_wr = {3'b111};
		}
		
		cmd_x_bank 					: cross cmd, bank;
		cmd_x_row  					: cross cmd, row;
		cmd_x_column 				: cross cmd, column;
		cmd_x_bank_x_row			: cross cmd, bank, row;
		cmd_x_bank_x_column			: cross cmd, bank, column;
		cmd_x_bank_x_row_x_column	: cross cmd, row, column, bank;
	endgroup
	
	covergroup sdram_cg @(posedge sdram_ctrl_intf.sdram_clk);
		
		bank : coverpoint sdram_ctrl_intf.sdr_ba
		{
			bins bank_0 = {0};
			bins bank_1 = {1};
			bins bank_2 = {2};
			bins bank_3 = {3};
		}
		
		cmd : coverpoint {sdram_ctrl_intf.sdr_cs_n, sdram_ctrl_intf.sdr_ras_n,sdram_ctrl_intf.sdr_cas_n,sdram_ctrl_intf.sdr_we_n}
		{
			bins inhibit		= {4'b1xxx};
			bins nop			= {4'b0111};
			bins active 		= {4'b0011};
			bins read 			= {4'b0101};
			bins write 			= {4'b0100};
			bins burst_ter  	= {4'b0110};
			bins recharge		= {4'b0010};
			bins auto_refresh 	= {4'b0001};
			bins load_mod_reg	= {4'b0000};
			bins misc			= default;
		}
		
		addr	: coverpoint sdram_ctrl_intf.sdr_addr;
		
		read_write_x_bank :	cross cmd, bank
		{
			ignore_bins my_ignore = binsof(cmd) intersect 
			{
				4'b1xxx,
				4'b0111,
				4'b0011,
				4'b0110,
				4'b0010,
				4'b0001,
				4'b0000
			};
		}
		
		read_write_x_addr : cross cmd, addr
		{
`ifdef SDR_08COL_BITS
			bins allowed_addrs 				= binsof(addr) intersect {[0:255]};
			bins incorrect_addrs 			= binsof(addr) intersect {[256:$]};
`elsif SDR_09COL_BITS
			bins allowed_addrs 				= binsof(addr) intersect {[0:511]};
			bins incorrect_addrs 			= binsof(addr) intersect {[512:$]};
`elsif SDR_10COL_BITS
			bins allowed_addrs 				= binsof(addr) intersect {[0:1023]};
			bins incorrect_addrs 			= binsof(addr) intersect {[1024:$]};
`else
			bins allowed_addrs 				= binsof(addr) intersect {[0:2047]};
			bins incorrect_addrs 			= binsof(addr) intersect {[2048:$]};
`endif
			ignore_bins my_ignore = binsof(cmd) intersect 
			{
				4'b1xxx,
				4'b0111,
				4'b0011,
				4'b0110,
				4'b0010,
				4'b0001,
				4'b0000
			};
		}
		
		read_write_x_bank_x_addr : cross cmd, bank, addr
		{
`ifdef SDR_08COL_BITS
			bins allowed_addrs 				= binsof(addr) intersect {[0:255]};
			bins incorrect_addrs 			= binsof(addr) intersect {[256:$]};
`elsif SDR_09COL_BITS
			bins allowed_addrs 				= binsof(addr) intersect {[0:511]};
			bins incorrect_addrs 			= binsof(addr) intersect {[512:$]};
`elsif SDR_10COL_BITS
			bins allowed_addrs 				= binsof(addr) intersect {[0:1023]};
			bins incorrect_addrs 			= binsof(addr) intersect {[1024:$]};
`else
			bins allowed_addrs 				= binsof(addr) intersect {[0:2047]};
			bins incorrect_addrs 			= binsof(addr) intersect {[2048:$]};
`endif
			ignore_bins my_ignore = binsof(cmd) intersect 
			{
				4'b1xxx,
				4'b0111,
				4'b0011,
				4'b0110,
				4'b0010,
				4'b0001,
				4'b0000
			};
		}
		
		open_banks : cross cmd, bank
		{
			ignore_bins my_ignore = binsof(cmd) intersect
			{
				4'b1xxx, // INHIBIT
				4'b0111, // NOP
				4'b0101, // READ
				4'b0100, // WRITE
				4'b0110, // BURST TERMINATE
				4'b0010, // RECHARGE
				4'b0001, // AUTOREFRES
				4'b0000  // LOAD MODE REGISTER
			};
		}
		
		open_rows : cross cmd, addr
		{
			ignore_bins my_ignore = binsof(cmd) intersect
			{
				4'b1xxx, // INHIBIT
				4'b0111, // NOP
				4'b0101, // READ
				4'b0100, // WRITE
				4'b0110, // BURST TERMINATE
				4'b0010, // RECHARGE
				4'b0001, // AUTOREFRES
				4'b0000  // LOAD MODE REGISTER
			};
		}
		
		open_banks_x_rows : cross cmd, bank, addr
		{
			ignore_bins my_ignore = binsof(cmd) intersect
			{
				4'b1xxx, // INHIBIT
				4'b0111, // NOP
				4'b0101, // READ
				4'b0100, // WRITE
				4'b0110, // BURST TERMINATE
				4'b0010, // RECHARGE
				4'b0001, // AUTOREFRESH
				4'b0000  // LOAD MODE REGISTER
			};
		}
		
		close_banks : cross cmd, bank
		{
			ignore_bins my_ignore = binsof(cmd) intersect
			{
				4'b1xxx, // INHIBIT
				4'b0111, // NOP
				4'b0011, // ACTIVE
				4'b0101, // READ
				4'b0100, // WRITE
				4'b0110, // BURST TERMINATE
				4'b0001, // AUTOREFRESH
				4'b0000  // LOAD MODE REGISTER
			};
		}
		
	endgroup
	
	
	function new(virtual sdrc_if sdram_ctrl_intf);
		this.sdram_ctrl_intf = sdram_ctrl_intf;
		
		// Cover points for test all banks
		this.wish_bone_cg = new();
		this.sdram_cg = new();
	endfunction
	
 endclass

`endif