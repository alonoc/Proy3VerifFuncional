`ifndef ENV_SV
`define ENV_SV

`include "sdrc_intf.sv"
`include "driver.sv"
`include "monitor.sv"
`include "scoreboard.sv"
`include "covergroups_sdram_ctrl.sv"

class environment;
	driver drv;
	scoreboard sb;
	monitor mon;
	covergroups_sdram_ctrl cov_groups_sdr;
    stimulusAllRand stAllRand;
	virtual sdrc_if intf;
	
	function new(virtual sdrc_if intf);
		this.intf = intf;
		sb = new();
		drv = new(intf, sb);
		mon = new(intf, sb);
		cov_groups_sdr = new(intf);
        stAllRand = new();
	endfunction
	
endclass

`endif
