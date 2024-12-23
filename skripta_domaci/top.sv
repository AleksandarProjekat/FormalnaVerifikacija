module top(
    input logic clk,
    input logic rst,

    // Zadatak 1 signals
    output logic rt1,
    output logic rdy1,
    output logic start1,
    output logic endd1,
    output logic help1,

    // Zadatak 2 signals 
    output logic er2,

    // Zadatak 3 signals 
    output logic er3,
    output logic rdy3,

    // Zadatak 4 signals
    output logic rdy4,
    output logic start4,

    // Zadatak 5 signals
    output logic endd5,
    output logic stop5,
    output logic er5,
    output logic rdy5,
    output logic start5,
    
    // Zadatak 6 signals
    output logic endd6,
    output logic stop6,
    output logic er6,
    output logic rdy6,

    // Zadatak 7 signals
    output logic endd7,
    output logic start7,
    output logic status_valid7,
    output logic instartsv7,

    // Zadatak 8 signals
    output logic rt8,
    output logic enable8,

    // Zadatak 9 signals
    output logic rdy9,
    output logic start9,
    output logic interrupt9,

    // Zadatak 10 singals
    output logic ack10,
    output logic req10
);

    counter uufv
    (
     .clk(clk),
     .rst(rst),
     .rt1(rt1),
     .rdy1(rdy1),
     .start1(start1),
     .help1(help1),
     .endd1(endd1),
     .er2(er2),
     .er3(er3),
     .rdy3(rdy3),
     .rdy4(rdy4),
     .start4(start4),
     .endd5(endd5),
     .stop5(stop5),
     .er5(er5),
     .rdy5(rdy5),
     .start5(start5),
     .endd6(endd6),
     .stop6(stop6),
     .er6(er6),
     .rdy6(rdy6),
     .endd7(endd7),
     .start7(start7),
     .status_valid7(status_valid7),
     .instartsv7(instartsv7),
     .rt8(rt8),
     .enable8(enable8),
     .rdy9(rdy9),
     .start9(start9),
     .interrupt9(interrupt9),
     .ack10(ack10),
     .req10(req10)	
);

default clocking @(posedge clk); endclocking
default disable iff(rst);

// Write properties here 
property p1;
	(rt1) && (help1) |-> ~(rdy1 || start1 || endd1);
endproperty
assert property (p1);

property p2;
	er2[*3] |=> !er2;
endproperty
assert property (p2);

property p3;
	er3 && rdy3 |=> !rdy3 || !er3;
endproperty
assert property (p3);

property p4;
	(start4 ##1 (1'b1)) |-> !rdy4[*0:10];
endproperty
assert property (p4);

property p5;
	(endd5 or stop5 or er5) |=> !rdy5;
endproperty
assert property (p5);

property p6;
	(endd6 || er6 || stop6) |-> rdy6; 
endproperty
assert property (p6);

property p7;
	endd7 |-> (!start7 && !status_valid7); 
endproperty
assert property (p7);

property p8;
	(rt8 |-> !enable8);
endproperty
assert property (p8);

property p9;
	interrupt9 |=> (!rdy9 && !start9);
endproperty
assert property (p9);

property p10;
	req10 |-> ##5 ack10;
endproperty
assert property (p10);



endmodule
