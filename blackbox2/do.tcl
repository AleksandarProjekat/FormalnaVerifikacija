clear -all

analyze -sv09 v_bb_model.v
analyze -sv09 checker.sv bind.sv

elaborate -top v_bb_model -lrm_cover_property

clock CLK
reset RST

prove -bg -all

