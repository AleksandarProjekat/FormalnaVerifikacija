checker sv_model_checker (clk, rst, x, y);

  logic          clk;
  logic          rst;
  logic [1023:0] x;
  logic [1023:0] y;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // 1) Every time y0 is 1, next cycle y0 is 0.
  p1: assert property ( y[0] |=> !y[0] );

  // 2) y2 will become 1 again and again.
  p2: assert property ( 1 |-> ##[1:$] y[2] );

  // 3) When y1 is 1, from next cycle, y3 is 1 until y4 is 1.
  p3: assert property ( y[1] |=> ( y[3] until y[4] ) );

  // 4) When y2 is followed by y5, then next cycle y6 will be 1.
  sequence y2_then_y5;
    y[2] ##1 y[5];
  endsequence
  p4: assert property ( y2_then_y5 |=> y[6] );

  // 5) When y2 is deasserted for 3 cycles, y7 asserted in the same (3rd) cycle.
  p5: assert property ( (!y[2])[*3] |-> y[7] );


  // 6) After 2 or 3 repetitions of y8: next cycle y9=0, and next cycle y10=1.
  p6: assert property ( y[8][*2:3] |=> ( !y[9] ##1 y[10] ) );

  // 7) If y0 is 1 then next cycle y1 is 1; else y11 must be asserted (same cycle).
  p7: assert property (
  ( y[0] |=> y[1] ) or ( !y[0] |-> y[11] )
  );


  // 8) Just right 2nd non-consecutive repetition of y2 -> next cycle y16 asserted.
  //Assert 8 – Level-based
  p8_level: assert property ( y[2][->2] |=> y[16] );
 

  // 9) Next cycle of 3rd non-consecutive repetition of all ones on y28-y17 -> y15 asserted.
  p9: assert property ( (&y[28:17])[->3] |=> y[15] );

  // 10) Cover: y29 asserted 10 consecutive cycles.
  p10: cover property ( y[29][*10] );

  // 11) y31-y30 are never 11; assume x1 and x0 mutually exclusive.
  p11a: assume property ( !(x[0] && x[1]) );
  p11b: assert  property ( !(y[31] && y[30]) );

endchecker

