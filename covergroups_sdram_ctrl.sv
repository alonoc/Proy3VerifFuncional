`ifndef COVERGROUP_SDRC_SV
`define COVERGROUP_SDRC_SV

`include "sdrc_intf.sv"

class covergroups_sdram_ctrl;
	
	virtual sdrc_if sdram_ctrl_intf;
	
	covergroup wb_addr @(posedge sdram_ctrl_intf.sys_clk);
		
		column	: coverpoint sdram_ctrl_intf.wb_addr_i[11:0]
		{
			bins valid_columns 		= { [0:7] };
			bins invalid_columns 	= { [8:$] };
		}
		
		bank 	: coverpoint sdram_ctrl_intf.wb_addr_i[13:12]
		{
			bins bank_0	= {0};
			bins bank_1	= {1};
			bins bank_2	= {2};
			bins bank_3	= {3};
		}
		
		row		: coverpoint sdram_ctrl_intf.wb_addr_i[25:14]
		{
			bins valid_rows 	= { [0:10] };
			bins invalid_rows 	= { [11:$] };
		}
		
	endgroup
	
	function new(virtual sdrc_if sdram_ctrl_intf);
		this.sdram_ctrl_intf = sdram_ctrl_intf;
		this.wb_addr = new();
	endfunction
	
 endclass

`endif