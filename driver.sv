`ifndef DRIVER_SV
`define DRIVER_SV

`include "sdrc_intf.sv"
`include "scoreboard.sv"
`include "stimulusAllRand.sv"
`include "stimulusRandAddr.sv"
`include "stimulusRowBank.sv"
`include "stimulusCrossOver.sv"

class driver;
    scoreboard sb;
    stimulusAllRand     stiAllRand;
    stimulusRandAddr    stiRandAddr;
    stimulusRowBank     stiRowBank;
    stimulusCrossOver   stiCrossOver;
    virtual sdrc_if intf;
    
    function new(virtual sdrc_if intf,scoreboard sb);
        this.intf = intf;
        this.stiAllRand = new();
        this.stiRandAddr = new();
        this.stiRowBank = new();
        this.stiCrossOver = new();
        this.sb = sb;
    endfunction
    
    task reset();  // Reset method
        intf.wb_addr_i = 0;
        intf.wb_dat_i  = 0;
        intf.wb_sel_i  = 4'h0;
        intf.wb_we_i   = 0;
        intf.wb_stb_i  = 0;
        intf.wb_cyc_i  = 0;

        intf.wb_rst_i = 1'h1;
        #100
        intf.wb_rst_i = 1'h0;
        #10000;
        intf.wb_rst_i = 1'h1;
        #1000;
        wait(intf.sdr_init_done == 1);
        #1000;
    endtask

    task write_routine(input int unsigned bl, input stimulus sti);
        int unsigned address;
        for(int i=0; i < bl; i++)
        begin
            address = sti.popAddress();   

            intf.wb_stb_i        = 1;
            intf.wb_cyc_i        = 1;
            intf.wb_we_i         = 1;
            intf.wb_sel_i        = 4'b1111;
            intf.wb_addr_i       = address;
            intf.wb_dat_i        = $random & 32'hFFFFFFFF;
            
            sb.afifo.push_back(intf.wb_addr_i);
            sb.dfifo[intf.wb_addr_i] = intf.wb_dat_i;// send written value to scoreboard

            do begin
                @ (posedge intf.sys_clk);
            end while(intf.wb_ack_o == 1'b0);

            @ (negedge intf.sys_clk);
            $display("Status: Burst-No: %d  WriteAddress: %x  WriteData: %x ", i, intf.wb_addr_i, intf.wb_dat_i);
        end
        intf.wb_stb_i        = 0;
        intf.wb_cyc_i        = 0;
        intf.wb_we_i         = 'hx;
        intf.wb_sel_i        = 'hx;
        intf.wb_addr_i       = 'hx;
        intf.wb_dat_i        = 'hx;
    endtask

    task testGen();
        int baseRow = 0;
        int baseCol = 8'hFF;
        int addr;

        int j;       //32'h0017_0FAC
        for(int i = 0, j = 0; i < 24; i++, j+=4)
        begin
            addr = ((baseRow & 8'hFF) << 16) | ((baseCol & 8'hFF) << 4) | (j & 4'hF);
            $display("Addr: %H", addr);
            
            baseRow += 1;
            if(j > 11) begin
                j = -4;
                baseCol -= 1;
            end
        end
    endtask

    task testRandomize();
        stimulus sti = stiAllRand;
        for(int i = 0; i < 20; i++)
        begin
            assert(sti.randomize());
            sti.burst_length = i + 1;
            $display("---------------------------------------------");
            $display("row: %d, col: %d, bank: %d", sti.getRow(0), sti.getCol(0), sti.getBank(0));
            //$display("row: %d, col: %d, bank: %d", sti.row, sti.col, sti.bank);
            $display("Randomized val: 0x%x, burst: %d", sti.getAddress(), sti.getBurstLength());
            $display("---------------------------------------------");
        end
    endtask

    task Burst_write(input int unsigned a, input int unsigned b);
    endtask

    task single_write(input int unsigned bl = 1);
        stimulus sti = stiRandAddr;
        sti.burst_length = bl;

        if(sti.randomize() != 1) begin
            $display("failed randomize()");
        end

        sb.bfifo.push_back(bl);
        
        @ (negedge intf.sys_clk);
        $display("Base Write Address: %x, Burst Size: %d", sti.getAddress(), bl);
        
        write_routine(bl, sti);
    endtask
    
    task all_rand_write();
        int unsigned address;
        int unsigned bl;
        stimulus sti = stiAllRand;

        if(sti.randomize() != 1) begin
            $display("failed randomize()");
        end

        bl = sti.getBurstLength();

        sb.bfifo.push_back(bl);
        
        @ (negedge intf.sys_clk);
        $display("Base Write Address: %x, Burst Size: %d", sti.getAddress(), bl);
        
        write_routine(bl, sti);
    endtask

    task crossover_write(output int writeCount);
        stimulus sti = stiCrossOver;
        int unsigned bl = sti.getBurstLength();
       
        @ (negedge intf.sys_clk);
        $display("Base Write Address: %x, Write Count: %d, Burst Size: 15", sti.getAddress(), bl);
        
        for(int i = 0; i < bl; i++)
        begin
            write_routine(4'hF, sti);
            sb.bfifo.push_back(4'hF);
        end
        writeCount = bl;
    endtask

    task rowbank_write(input int unsigned rw, input int unsigned bnk);
        int unsigned bl;
        stimulus sti = stiRowBank;
        
        sti.setRow(rw);
        sti.setBank(bnk);

        if(sti.randomize() != 1) begin
            $display("failed randomize()");
        end

        bl = sti.getBurstLength();
        sb.bfifo.push_back(bl);
        
        @ (negedge intf.sys_clk);
        $display("Base Write Address: %x, Burst Size: %d", sti.getAddress(), bl);
        
        write_routine(bl, sti);
    endtask
    
endclass

`endif
