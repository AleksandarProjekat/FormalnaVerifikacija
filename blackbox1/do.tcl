clear -all
analyze -sv09 sv_model.sv
analyze -sv09 checker.sv bind.sv

elaborate -top sv_model -lrm_cover_property
clock clk
reset rst
prove -bg -all 
