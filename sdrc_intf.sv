`ifndef SDRC_IF_SV
`define SDRC_IF_SV

interface sdrc_if #(
    parameter APP_AW=26,    // Application Address Width
    parameter SDR_DW=32,    // SDR Data Width 
    parameter SDR_BW=4,     // SDR Byte Width
    parameter dw=32)        // data width
    (sys_clk, sdram_clk);
    
    // Clocks
    input sys_clk;
    input sdram_clk;    
    
    // WISH BONE BUS PORTS
    logic wb_rst_i;
    logic wb_stb_i;
	logic wb_we_i;
	logic wb_cyc_i;
	logic [2:0] wb_cti_i;
	logic [dw-1:0] wb_dat_i;
	logic [dw/8-1:0] wb_sel_i;
    logic [APP_AW-1:0] wb_addr_i;

    wire wb_ack_o;
    wire [dw-1:0] wb_dat_o;
    
    // SDRAM PORTS
    logic sdr_cs_n;
    logic sdr_cke;
    logic sdr_ras_n;
    logic sdr_cas_n;
    logic sdr_we_n;
	
    wire [1:0] sdr_ba;
    wire [12:0] sdr_addr;
    wire [SDR_BW-1:0] sdr_dqm;
    wire [SDR_DW-1:0] sdr_dq;
    
    // PARAMETERS
    wire sdr_init_done;
	
endinterface : sdrc_if

`endif
