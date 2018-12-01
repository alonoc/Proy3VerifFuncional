`ifndef STIMULUS_SV
`define STIMULUS_SV

virtual class stimulus;
    int burst_length;

    //returns first address, without modifying queues
    pure virtual function integer getAddress();
    
    //pops next address from queues
    pure virtual function integer popAddress();

    //getters/setters, necessary because direct access goes for members in base class
    pure virtual function integer getRow(idx);
    pure virtual function integer getCol(idx);
    pure virtual function integer getBank(idx);
    pure virtual function integer getBurstLength();

    pure virtual function integer setRow(val);
    pure virtual function integer setCol(val);
    pure virtual function integer setBank(val);

    // memory layout
    // sdram controller supports the following amount of rows, banks, and columns:
    //                              4M*16 Config ->       12     4           8
    //                              2M*32 Config ->       11     4           8
    
    // Row Address[11:0] Bank Address[1:0] Column Address[11:0]

endclass

`endif
