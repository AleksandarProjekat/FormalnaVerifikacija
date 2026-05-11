clear -all
analyze -sv09 +define+FORMAL checker.sv
elaborate -top {sort_ip_formal_top}
clock clk
reset rst
prove -bg -all

