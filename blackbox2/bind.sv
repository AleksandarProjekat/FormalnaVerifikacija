bind v_bb_model v_bb_props u_props (
  .CLK(CLK),
  .RST(RST),
  .STALL(STALL),
  .REQ(REQ),
  .OPCH(OPCH),

  .OPS(OPS),
  .TEST(TEST),
  .AB(AB),
  .BC(BC),
  .CD(CD),
  .ERR(ERR),
  .ACK(ACK),
  .BUSY(BUSY),
  .DONE(DONE),
  .DATA(DATA),

  .ack_next(ack_next),
  .unacked_reqs(unacked_reqs),
  .state_reg(state_reg),
  .cnt(cnt),
  ._000_(_000_)
);

