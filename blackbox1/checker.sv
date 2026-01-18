checker sv_model_checker (
    clk,
     rst,
    x,y
);

default clocking cb @(posedge clk); endclocking
    default disable iff (rst);

    // 1) Every time y0 is 1, next cycle y0 is 0.
    p1: assert property ( y[0] |=> !y[0] );

    // 2) y2 will become 1 again and again.
    p2: assert property ( always s_eventually (y[2]) );

    // 3) When y1 is 1, from next cycle y3 is 1 until y4 is 1.
    p3: assert property ( y[1] |=> (y[3] until_with y[4]) );

    // 4) When y2 is followed by y5, next cycle y6 will be 1.
    p4: assert property ( (y[2] ##1 y[5]) |=> y[6] );

    // 5) When y2 is deasserted for 3 cycles, y7 has to be asserted in the same cycle.
    p5: assert property ( (!y[2])[*3] |-> y[7] );

    // 6) After 2 or 3 repetitions of y8, y9 must be 0,
    // and the cycle after that y10 must be 1.
    p6: assert property ( y[8][*2:3] ##1 (!y[9]) ##1 y[10] );

    // 7) If y0 is 1, next cycle y1 is 1; else (if y0 is 0), y11 must be asserted.
    p7: assert property ( y[0] ? (##1 y[1]) : (y[11]) );

    // 8) Just right 2nd non-consecutive repetition of y2 next cycle y16 will be asserted.
    p8: assert property ( y[2][->2] |=> y[16] );

    // 9) Next cycle of 3rd non-consecutive repetition of all ones on y28-y17, 
    //y15 will be asserted.
    p9: assert property ( (&y[28:17])[->3] |=> y[15] );

    // 10) It will happen that y29 is asserted 10 consecutive cycles.
    p10: cover property ( y[29][*10] );

    // 11) y31-y30 are never 11 - but it needs assume that x1 and x0 are mutually
    //exclusive. Run without assume, then interactively add that assumption, and see the
    //difference
    p11a: assume property ( x[0] ^ x[1] );
    p11b: assert property ( !(y[31] && y[30]) );

endchecker

