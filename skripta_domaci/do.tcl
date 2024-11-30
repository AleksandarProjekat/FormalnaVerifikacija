analyze -sv09 counter.sv
analyze -sv09 top.sv
elaborate -top {top}
clock clk
reset rst
prove -bg -all
