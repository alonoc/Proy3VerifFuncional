`ifndef SCOREBOARD_SV
`define SCOREBOARD_SV

class scoreboard;
	int unsigned dfifo[int]; // data fifo, indexed by address
	int unsigned afifo[$]; // address  fifo
	int unsigned bfifo[$]; // Burst Length fifo
    
    // Control flags
    int unsigned error_count;
    int unsigned loop_count;
    
    function new();
		this.error_count = 0;
        this.loop_count = 0;
	endfunction

    function clear();
        this.error_count = 0;
        this.loop_count = 0;
        this.dfifo.delete();
        this.afifo = {};
        this.bfifo = {};
    endfunction
    
endclass

`endif
