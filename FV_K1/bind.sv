// Vezuje checker module sa black_box entitetom
bind black_box black_box_checker c0(.clk(clk), .rst(rst), 
                                    .a1(a1), .a2(a2), .a3(a3), .a4(a4), .a5(a5),
                                    .cntA(cntA), .cntB(cntB), 
                                    .b1(b1), .b2(b2), .b3(b3),
                                    .c1(c1), .c2(c2), .c3(c3), .c4(c4), .c5(c5), .c6(c6),
                                    .d1(d1), .d2(d2), .d3(d3), .d4(d4), .d5(d5));
