# Očisti prethodno stanje i pripremi novo okruženje
clear -all

# Analiziraj SystemVerilog fajlove
analyze -sv09 checker.sv bind.sv hw_blok.sv

# Elaboriraj dizajn sa top-level modulom sort_ip
elaborate -sv09 -top sort_ip -lrm_cover_property

# Definiši clock i reset signale
clock clk
reset resetn

# Pokreni formalnu proveru svih asertacija
prove -bg -all

# Generiši HTML izveštaj o rezultatima
report_results -html -o axi_sorting_report.html

