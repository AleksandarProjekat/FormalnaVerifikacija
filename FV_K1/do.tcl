clear -all
analyze -sv09 checker.sv bind.sv
analyze -vhdl black_box.vhd
elaborate -vhdl -top black_box -lrm_cover_property
clock clk
reset reset
prove -bg -all 
