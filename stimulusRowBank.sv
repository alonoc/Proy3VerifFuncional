`ifndef STIMULUS_ROWBANK_SV
`define STIMULUS_ROWBANK_SV

`include "stimulus.sv"

class stimulusRowBank extends stimulus;
    bit[11:0] row;
    bit[1:0]  bank;
    rand  bit[11:0] col[$];

    randc int burst_length; //cyclic

    constraint burst {
        this.burst_length inside {[4:7]};
    }

    constraint arrayBounds {
        col.size == this.burst_length;
    }

    constraint memoryRange {
        foreach(col[i]) { col[i] inside {[0:7]} };
    }

    function new();
        this.row = 0;
        this.bank = 0;
    endfunction
    
    function integer getRow(idx);
        return this.row;
    endfunction
    function integer getCol(idx);
        return this.col[idx];
    endfunction
    function integer getBank(idx);
        return this.bank;
    endfunction
    function integer getBurstLength();
        return this.burst_length;
    endfunction

	function integer setRow(val);
        this.row = val;
    endfunction
    function integer setBank(val);
        this.bank = val;
	endfunction
    function integer setCol(val);
    endfunction

    //returns first address, without modifying queues
    function integer getAddress();
        return {this.row, this.bank, this.col[0]};
        //return (this.row << 14) | (this.bank << 12) | (this.col[0]); this is the same as above
    endfunction

    //pops next address from queues
    function integer popAddress();
        return {this.row, this.bank, this.col.pop_front()};
    endfunction

    // memory layout
    // sdram controller supports the following amount of rows, banks, and columns:
    //                              4M*16 Config ->       12     4           8
    //                              2M*32 Config ->       11     4           8
    
    // Row Address[11:0] Bank Address[1:0] Column Address[11:0]

endclass

`endif
