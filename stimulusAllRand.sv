`ifndef STIMULUS_ALLRAND_SV
`define STIMULUS_ALLRAND_SV

`include "stimulusRandAddr.sv"

class stimulusAllRand extends stimulusRandAddr;
    rand  bit[11:0] row[$];
    rand  bit[1:0]  bank[$];
    rand  bit[11:0] col[$];

    rand int burst_length;

    constraint burst {
        this.burst_length inside {[0:15]};
    }

    constraint arrayBounds {
        bank.size == this.burst_length;
        row.size == this.burst_length;
        col.size == this.burst_length;
    }

    constraint memoryRange {
        foreach(bank[i]) { bank[i] inside {[0:4]} };
        foreach(row[i]) { row[i] inside {[0:11]} };
        foreach(col[i]) { col[i] inside {[0:7]} };
    };
    
    function integer getRow(idx);
        return this.row[idx];
    endfunction
    function integer getCol(idx);
        return this.col[idx];
    endfunction
    function integer getBank(idx);
        return this.bank[idx];
    endfunction
    function integer getBurstLength();
        return this.burst_length;
    endfunction

    function integer setRow(val);
    endfunction
    function integer setCol(val);
    endfunction
    function integer setBank(val);
    endfunction

    //returns first address, without modifying queues
    function integer getAddress();
        return {this.row[0], this.bank[0], this.col[0]};
        //return (this.row[0] << 14) | (this.bank[0] << 12) | (this.col[0]); this is the same as above
    endfunction

    //pops next address from queues
    function integer popAddress();
        return {this.row.pop_front(), this.bank.pop_front(), this.col.pop_front()};
    endfunction

    // memory layout
    // sdram controller supports the following amount of rows, banks, and columns:
    //                              4M*16 Config ->       12     4           8
    //                              2M*32 Config ->       11     4           8
    
    // Row Address[11:0] Bank Address[1:0] Column Address[11:0]

endclass

`endif
