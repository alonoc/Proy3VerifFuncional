`ifndef STIMULUS_ALLRAND_SV
`define STIMULUS_ALLRAND_SV

`include "stimulusRandAddr.sv"

class stimulusAllRand extends stimulusRandAddr;

	rand int burst_length;
	rand  bit[11:0] row[$];
	rand  bit[1:0]  bank[$];
	
`ifdef SDR_08COL_BITS
	rand  bit[7:0] col[$];
`elsif SDR_09COL_BITS
	rand  bit[8:0] col[$];
`elsif SDR_10COL_BITS
	rand  bit[9:0] col[$];
`else
	rand  bit[10:0] col[$];
`endif
	
    constraint burst {
        this.burst_length inside {[0:15]};
    }
	
    constraint arrayBounds {
        bank.size == this.burst_length;
        row.size == this.burst_length;
        col.size == this.burst_length;
    }
	
    constraint memoryRange 
	{
        foreach(bank[i]){ bank[i] inside {[0:3]} };
        foreach(row[i]) { row[i] inside {[0:4095]} };

`ifdef SDR_08COL_BITS
		foreach(col[i]) { col[i] inside {[0:255]} };
`elsif SDR_09COL_BITS
		foreach(col[i]) { col[i] inside {[0:511]} };
`elsif SDR_10COL_BITS
		foreach(col[i]) { col[i] inside {[0:1023]} };
`else
		foreach(col[i]) { col[i] inside {[0:2047]} };
`endif
	
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
    endfunction
	
    //pops next address from queues
    function integer popAddress();
        return {this.row.pop_front(), this.bank.pop_front(), this.col.pop_front()};
    endfunction

endclass

`endif
