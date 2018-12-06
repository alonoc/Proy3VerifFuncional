`ifndef WHITEBOX_INTF_SV
`define WHITEBOX_INTF_SV

interface whitebox_intf (   sdram_clk, sdram_rst, sdram_ras_n, sdram_cas_n, sdram_we_n,sdram_dq,
                            sdram_cas, sdram_trcar_d, sdram_rfsh, sdram_rfmax,
                            wb_clk_i, wb_rst_i, wb_stb_i, wb_ack_o, wb_addr_i, wb_we_i,
                            wb_dat_i, wb_sel_i, wb_dat_o, wb_cyc_i, wb_cti_i);
    
    //SDRAM Signals
    input sdram_clk;
    input sdram_rst;
    input sdram_ras_n;
    input sdram_cas_n;
    input sdram_we_n;
    input sdram_dq;

    //SDRAM Parameters
    input sdram_cas;
    input sdram_trcar_d;
    input sdram_rfsh;
    input sdram_rfmax;
    
    // Wishbone Signals
    input wb_clk_i;
    input wb_rst_i;
    input wb_stb_i;
    input wb_ack_o;
    input wb_addr_i;
    input wb_we_i;
    input wb_dat_i;
    input wb_sel_i;
    input wb_dat_o;
    input wb_cyc_i;
    input wb_cti_i;

endinterface : whitebox_intf

`endif
