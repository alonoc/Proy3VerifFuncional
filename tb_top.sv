`timescale 1ns/1ps

`include "sdrc_intf.sv"
`include "whitebox_intf.sv"
`include "assertions.v"
`include "test.sv"

module tb_top();

`define SDR_16BIT

// Clocks
parameter P_SYS = 10;     //    200MHz
parameter P_SDR = 20;     //    100MHz
reg sdram_clk;
reg sys_clk;

initial sys_clk = 0;
initial sdram_clk = 0;

always #(P_SYS/2) sys_clk = !sys_clk;
always #(P_SDR/2) sdram_clk = !sdram_clk;

// to fix the sdram interface timing issue
wire #(2.0) sdram_clk_d   = sdram_clk;

`ifdef SDR_32BIT
    sdrc_if #(26,32, 4,32) SdrcIntf(sys_clk, sdram_clk); // 32 BIT SDRC INTF
`elsif SDR_16BIT
    sdrc_if #(26,16, 2,32) SdrcIntf(sys_clk, sdram_clk); // 16 BIT SDRC INTF
`else 
    sdrc_if #(26, 8, 1,32) SdrcIntf(sys_clk, sdram_clk); //  8 BIT SDRC INTF
`endif

`ifdef SDR_32BIT
    sdrc_top #(.SDR_DW(32),.SDR_BW(4)) u_dut(
        .cfg_sdr_width      (2'b00                  ),  // 32 BIT SDRAM
`elsif SDR_16BIT 
    sdrc_top #(.SDR_DW(16),.SDR_BW(2)) u_dut(
        .cfg_sdr_width      (2'b01                  ),  // 16 BIT SDRAM
`else  // 8 BIT SDRAM
    sdrc_top #(.SDR_DW(8),.SDR_BW(1))  u_dut(
        .cfg_sdr_width      (2'b10                  ),  // 8 BIT SDRAM
`endif

`ifdef SDR_08COL_BITS
        .cfg_colbits        (2'b00                  ),  // 08 Bit Column Address
`elsif SDR_09COL_BITS
        .cfg_colbits        (2'b01                  ),  // 09 Bit Column Address
`elsif SDR_10COL_BITS
        .cfg_colbits        (2'b10                  ),  // 10 Bit Column Address
`else
        .cfg_colbits        (2'b11                  ),  // 11 Bit Column Address
`endif
        
        // Wishbone
        .wb_rst_i           (!SdrcIntf.wb_rst_i     ),
        .wb_clk_i           (SdrcIntf.sys_clk       ),
        .wb_stb_i           (SdrcIntf.wb_stb_i      ),
        .wb_ack_o           (SdrcIntf.wb_ack_o      ),
        .wb_addr_i          (SdrcIntf.wb_addr_i     ),
        .wb_we_i            (SdrcIntf.wb_we_i       ),
        .wb_dat_i           (SdrcIntf.wb_dat_i      ),
        .wb_sel_i           (SdrcIntf.wb_sel_i      ),
        .wb_dat_o           (SdrcIntf.wb_dat_o      ),
        .wb_cyc_i           (SdrcIntf.wb_cyc_i      ),
        .wb_cti_i           (SdrcIntf.wb_cti_i      ),
        
        // SDRAM
        .sdram_clk          (SdrcIntf.sdram_clk     ),
        .sdram_resetn       (SdrcIntf.wb_rst_i      ),
        .sdr_cs_n           (SdrcIntf.sdr_cs_n      ),
        .sdr_cke            (SdrcIntf.sdr_cke       ),
        .sdr_ras_n          (SdrcIntf.sdr_ras_n     ),
        .sdr_cas_n          (SdrcIntf.sdr_cas_n     ),
        .sdr_we_n           (SdrcIntf.sdr_we_n      ),
        .sdr_dqm            (SdrcIntf.sdr_dqm       ),
        .sdr_ba             (SdrcIntf.sdr_ba        ),
        .sdr_addr           (SdrcIntf.sdr_addr      ), 
        .sdr_dq             (SdrcIntf.sdr_dq        ),
        
        // Parameters
        .sdr_init_done      (SdrcIntf.sdr_init_done ),
        .cfg_req_depth      (2'h3                   ),  //how many req. buffer should hold
        .cfg_sdr_en         (1'b1                   ),
        .cfg_sdr_mode_reg   (13'h033                ),
        .cfg_sdr_tras_d     (4'h4                   ),
        .cfg_sdr_trp_d      (4'h2                   ),
        .cfg_sdr_trcd_d     (4'h2                   ),
        .cfg_sdr_cas        (3'h3                   ),
        .cfg_sdr_trcar_d    (4'h7                   ),
        .cfg_sdr_twr_d      (4'h1                   ),
        .cfg_sdr_rfsh       (12'h100                ), // reduced from 12'hC35
        .cfg_sdr_rfmax      (3'h6                   )
);

`ifdef SDR_32BIT
    mt48lc2m32b2 #(.data_bits(32)) u_sdram32 (
        .Dq                 (SdrcIntf.sdr_dq        ), 
        .Addr               (SdrcIntf.sdr_addr[10:0]), 
        .Ba                 (SdrcIntf.sdr_ba        ), 
        .Clk                (sdram_clk_d            ), 
        .Cke                (SdrcIntf.sdr_cke       ), 
        .Cs_n               (SdrcIntf.sdr_cs_n      ), 
        .Ras_n              (SdrcIntf.sdr_ras_n     ), 
        .Cas_n              (SdrcIntf.sdr_cas_n     ), 
        .We_n               (SdrcIntf.sdr_we_n      ), 
        .Dqm                (SdrcIntf.sdr_dqm       )
     );

`elsif SDR_16BIT
   IS42VM16400K u_sdram16 (
        .dq                 (SdrcIntf.sdr_dq        ), 
        .addr               (SdrcIntf.sdr_addr[11:0]), 
        .ba                 (SdrcIntf.sdr_ba        ), 
        .clk                (sdram_clk_d            ), 
        .cke                (SdrcIntf.sdr_cke       ), 
        .csb                (SdrcIntf.sdr_cs_n      ), 
        .rasb               (SdrcIntf.sdr_ras_n     ), 
        .casb               (SdrcIntf.sdr_cas_n     ), 
        .web                (SdrcIntf.sdr_we_n      ), 
        .dqm                (SdrcIntf.sdr_dqm       )
    );
`else
    mt48lc8m8a2 #(.data_bits(8)) u_sdram8 (
        .Dq                 (SdrcIntf.sdr_dq        ), 
        .Addr               (SdrcIntf.sdr_addr[11:0]), 
        .Ba                 (SdrcIntf.sdr_ba        ), 
        .Clk                (sdram_clk_d            ), 
        .Cke                (SdrcIntf.sdr_cke       ), 
        .Cs_n               (SdrcIntf.sdr_cs_n      ), 
        .Ras_n              (SdrcIntf.sdr_ras_n     ), 
        .Cas_n              (SdrcIntf.sdr_cas_n     ), 
        .We_n               (SdrcIntf.sdr_we_n      ), 
        .Dqm                (SdrcIntf.sdr_dqm       )
     );
`endif

whitebox_intf wbox_intf
(
		// SDRAM signals
		.sdram_clk			(sdrc_top.sdram_clk		),
		.sdram_rst			(sdrc_top.sdram_resetn	),
		.sdram_ras_n		(sdrc_top.sdr_ras_n		), 
		.sdram_cas_n		(sdrc_top.sdr_cas_n		), 
		.sdram_we_n			(sdrc_top.sdr_we_n		),
		.sdram_dq			(sdrc_top.sdr_dq),
		//SDRAMS parameters
		.sdram_cas 			(sdrc_top.cfg_sdr_cas),
        .sdram_trcar_d      (sdrc_top.cfg_sdr_trcar_d),
        .sdram_rfsh         (sdrc_top.cfg_sdr_rfsh  ),
        .sdram_rfmax        (sdrc_top.cfg_sdr_rfmax ),
		// WISHBONE signals
		.wb_clk_i			(sdrc_top.wb_clk_i		),
		.wb_rst_i			(sdrc_top.wb_rst_i		),
		.wb_stb_i			(sdrc_top.wb_stb_i		),
		.wb_ack_o			(sdrc_top.wb_ack_o		),
		.wb_addr_i			(sdrc_top.wb_addr_i		),
		.wb_we_i			(sdrc_top.wb_we_i		),
		.wb_dat_i			(sdrc_top.wb_dat_i		),
		.wb_sel_i			(sdrc_top.wb_sel_i		),
		.wb_dat_o			(sdrc_top.wb_dat_o		),
		.wb_cyc_i			(sdrc_top.wb_cyc_i		),
		.wb_cti_i			(sdrc_top.wb_cti_i		)
);

assertions assert_module(wbox_intf);

initial begin
    $display("-------------------------------------- ");
      $display("          Simulation: Started          ");
      $display("-------------------------------------- ");
end

test t1(SdrcIntf);

endmodule

