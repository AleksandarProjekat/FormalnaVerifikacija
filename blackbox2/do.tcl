clear -all
analyze -sv09 checker.sv bind.sv
analyze -sv09 v_bb_model.v
elaborate -sv09_expression_mode -top v_bb_model -lrm_cover_property
clock CLK
reset RST
prove -bg -all 
