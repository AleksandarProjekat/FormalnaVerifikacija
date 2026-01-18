bind sort_ip axi_sort_checker checker_inst (
  .clk(clk),
  .reset(resetn),
  .sort_dir(sort_dir),
  .ain_tdata(ain_tdata),
  .ain_tvalid(ain_tvalid),
  .ain_tready(ain_tready),
  .ain_tlast(ain_tlast),
  .aout_tdata(aout_tdata),
  .aout_tvalid(aout_tvalid),
  .aout_tready(aout_tready),
  .aout_tlast(aout_tlast),
  .dup_nums(dup_nums)
);

