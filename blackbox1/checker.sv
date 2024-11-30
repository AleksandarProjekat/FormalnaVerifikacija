checker sv_model_checker (
    clk,
     rst,
    x,y
);

    default clocking @(posedge clk);
    endclocking

    default disable iff (rst);

	logic t;


	always @ (posedge clk) begin
		if (y[29]) 
			t <= 1'b1;		
		else
			t <= 1'b0;		
	end

    // 1. Assert: Every time when y0 is 1, next cycle y0 is 0.
    p1: assert property ( y[0] |=> ~y[0] );

    // 2. Assert: y2 will become 1 again and again.
    p2: assert property (always s_eventually y[2]);

    // 3. Assert: When y1 is 1, from next cycle, y3 is 1 until y4 is 1.
    p3: assert property (y[1] |=>  y[3] until y[4]);

    // 4. Assert: When y2 is followed by y5, next cycle y6 will be 1.
    p4: assert property ((y[2] ##1 y[5]) |=> y[6]);

    // 5. Assert: When y2 is deasserted for 3 cycles, y7 has to be asserted in the same cycle.
    p5: assert property (~y[2] [*3] |-> y[7]);

    // 6. Assert: After 2 or 3 repetitions of y8, y9 must be 0, and then y10 must be 1.
    p6: assert property ((y[8] [*2:3] ##1 ~y[9]) |=> y[10]);

    // 7. Assert: If y0 is 1, next cycle y1 is 1; else, y11 must be asserted.
    p7: assert property (if(y[0]) ##1 y[1] else y[11]);

    // 8. Assert: On the 2nd non-consecutive repetition of y2, y16 will be asserted.
    p8: assert property (y[2] [->2] |=> y[16]);

    // 9. Assert: On the 3rd non-consecutive repetition of all ones on y28-y17, y15 will be asserted.
    p9: assert property (y[28:17] [->3] |=> y[15]);

    // 10. Cover: y29 is asserted for 10 consecutive cycles.
    p10: cover property (t |-> y[29] [*10]);

    // 11. Assert: y31 and y30 are never both 1, but assume x1 and x0 are mutually exclusive.
    p11a: assume property (x[0] ^ x[1]);
    p11b: assert property (!(y[31] && y[30]));

endchecker

