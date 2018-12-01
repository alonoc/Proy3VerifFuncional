`ifndef STIMULUS_CROSSOVER_SV
`define STIMULUS_CROSSOVER_SV

`include "stimulus.sv"

class stimulusCrossOver extends stimulus;
    int address[$];
    int unsigned burst_length[$];
    int numBurst;

    function new();
        numBurst = 24;
        CreateIt();
    endfunction

    function void CreateIt();
        int baseRow = 0;
        int baseCol = 8'hFF;
        int addr;

        int k;
        for(int i = 0, int j = 0; i < this.numBurst; i++, j+=4)
        begin
            addr = ((baseRow & 8'hFF) << 16) | ((baseCol & 8'hFF) << 4) | (j & 4'hF);
            this.burst_length.push_back(4'hF);

            for(k = 1; k < 15; k++)
            begin
                this.address.push_back(addr);
                addr += k;
            end
            
            baseRow += 1;
            if(j > 11) begin
                j = -4;
                baseCol -= 1;
            end
        end
    endfunction
    
    function integer getRow(idx);
        return ((this.address[idx]) >> 14) & 12'hFFF;
    endfunction
    function integer getCol(idx);
        return ((this.address[idx]) >> 12) & 2'h3;
    endfunction
    function integer getBank(idx);
        return (this.address[idx]) & 12'hFFF;
    endfunction
    function integer getBurstLength();
        return this.numBurst;
    endfunction

	function integer setRow(val);
    endfunction
    function integer setBank(val);
	endfunction
    function integer setCol(val);
    endfunction

    //returns first address, without modifying queues
    function integer getAddress();
        return this.address[0];
    endfunction

    //pops next address from queues
    function integer popAddress();
        return this.address.pop_front();
    endfunction

    // memory layout
    // sdram controller supports the following amount of rows, banks, and columns:
    //                              4M*16 Config ->       12     4           8
    //                              2M*32 Config ->       11     4           8
    
    // Row Address[11:0] Bank Address[1:0] Column Address[11:0]

endclass

`endif
