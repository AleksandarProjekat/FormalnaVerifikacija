clear -all
analyze -sv09 panex.sv
elaborate -top {panex}
clock clk
reset rst
set_engine_mode Tri
prove -property {panex.cover_done}
