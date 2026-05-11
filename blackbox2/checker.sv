module v_bb_props (
  input  wire        CLK,
  input  wire        RST,
  input  wire        STALL,
  input  wire        REQ,
  input  wire        OPCH,

  input  wire [3:0]  OPS,
  input  wire        TEST,
  input  wire        AB,
  input  wire        BC,
  input  wire        CD,
  input  wire        ERR,
  input  wire        ACK,
  input  wire        BUSY,
  input  wire        DONE,
  input  wire [2:0]  DATA,

  input  wire        ack_next,
  input  wire [2:0]  unacked_reqs,
  input  wire [4:0]  state_reg,
  input  wire [3:0]  cnt,
  input  wire        _000_
);

  default clocking cb @(posedge CLK);
  endclocking
  default disable iff (RST);

  // ============================================================
  // Assume:
  // Write any necessary assumptions for the inputs to ensure every assertion passes.
  // ============================================================

  a_req_pulse:      assume property ( REQ |-> ##1 !REQ );
  a_req_limit_5:    assume property ( (unacked_reqs >= 3'd5) |-> !REQ );
  a_stall_fair:     assume property ( STALL |-> ##[1:16] !STALL );

  // ============================================================
  // Assert:
  // Every REQ should have a corresponding ACK;
  // There can be up to 5 pending REQs;
  // When a REQ occurs, its corresponding ACK cannot occur in the same cycle;
  // When a REQ occurs, ACK of a previous REQ can occur in the same cycle.
  // ============================================================

  p_req_eventually_ack: assert property ( REQ |-> ##[1:64] ACK );

  p_no_samecycle_ack_when_empty: assert property (
    (REQ && ($past(unacked_reqs) == 3'd0)) |-> !ACK
  );

  p_pending_le_5: assert property ( unacked_reqs <= 3'd5 );

  // ============================================================
  // Assert:
  // While there are any pending REQs, BUSY is active.
  // ============================================================

  p_busy_when_pending: assert property ( (unacked_reqs != 3'd0) |-> BUSY );

  // ============================================================
  // Assert:
  // On the cycle following the last ACK, if there is no new REQ,
  // DONE is asserted for exactly one cycle.
  // ============================================================

  p_done_one_cycle: assert property ( _000_ |=> (DONE ##1 !DONE) );

  // ============================================================
  // Assert:
  // When DONE is asserted, DATA is stable.
  // ============================================================

  p_data_stable_on_done: assert property ( DONE |-> $stable(DATA) );

  // ============================================================
  // Assert:
  // When TEST is asserted, AB is repeated consecutively 3 times,
  // then after 3 to 4 cycles BC is repeated non-consecutively 3 to 4 times,
  // and after this, an arbitrary number of cycles may occur before CD rises.
  // ============================================================

  p_test_ab_bc_cd: assert property (
    TEST |=> ( AB[*3]
               ##[3:4]
               (BC[->3] or BC[->4])
               ##[0:$] $rose(CD) )
  );

  // ============================================================
  // Assert:
  // ERR is never active.
  // ============================================================

  p_err_never: assert property ( !ERR );

  // ============================================================
  // Assert:
  // OPS always has either no bits or only one bit set to 1.
  // ============================================================

  p_ops_onehot0: assert property ( $onehot0(OPS) );

  // ============================================================
  // Assert:
  // OPS changes according to the associated FSM.
  // ============================================================

  p_ops_0000_to_0001: assert property ( (!STALL && (OPS == 4'b0000)) |=> (OPS == 4'b0001) );

  p_ops_0001_to_0010: assert property ( (!STALL && (OPS == 4'b0001) &&  OPCH) |=> (OPS == 4'b0010) );

  p_ops_0001_to_0100: assert property ( (!STALL && (OPS == 4'b0001) && !OPCH) |=> (OPS == 4'b0100) );

  p_ops_0010_to_1000: assert property ( (!STALL && (OPS == 4'b0010)) |=> (OPS == 4'b1000) );

  p_ops_0100_to_1000: assert property ( (!STALL && (OPS == 4'b0100)) |=> (OPS == 4'b1000) );

  p_ops_1000_to_0000: assert property ( (!STALL && (OPS == 4'b1000)) |=> (OPS == 4'b0000) );

  // ============================================================
  // Assert:
  // If STALL is active, OPS does not change.
  // ============================================================

  p_ops_hold_on_stall: assert property ( STALL |=> (OPS == $past(OPS)) );

  // ============================================================
  // Cover:
  // 4 cycles after OPS is 0100, OPS is 0100 again.
  // ============================================================

  c_ops_0100_after_4: cover property ( (OPS == 4'b0100) ##4 (OPS == 4'b0100) );

endmodule

