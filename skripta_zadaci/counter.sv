module counter(
    input logic clk,
    input logic rst,

    output logic rt1, rdy1, start1, endd1, help1,       // Zadatak 1
    output logic er2,                                   // Zadatak 2
    output logic er3, rdy3,                             // Zadatak 3
    output logic rdy4, start4,                          // Zadatak 4
    output logic endd5, stop5, er5, rdy5, start5,       // Zadatak 5
    output logic endd6, stop6, er6, rdy6,               // Zadatak 6
    output logic endd7, start7, status_valid7, instartsv7, // Zadatak 7
    output logic rt8, enable8,                          // Zadatak 8
    output logic rdy9, start9, interrupt9,              // Zadatak 9
    output logic ack10, req10                           // Zadatak 10
);

    logic [3:0] count; // 4-bit counter, range 0-15

    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            count <= 0;
        else
            count <= count + 1;
    end

    // Zadatak 1
    assign rt1 = (count < 4) || (count == 8);
    assign rdy1 = (count == 5);
    assign start1 = (count == 8);
    assign endd1 = (count == 6);
    always_comb help1 = (count < 5);

    // Zadatak 2
    assign er2 = ((count >= 1 && count < 3) || (count >= 6 && count < 9));

    // Zadatak 3
    assign er3 = ((count == 1) || (count >= 5 && count < 7) || (count == 9));
    assign rdy3 = ((count >= 1 && count < 3) || (count == 5) || (count == 9));

    // Zadatak 4
    assign rdy4 = (count == 6);
    assign start4 = (count == 2);

    // Zadatak 5
    assign endd5 = (count == 2);
    assign stop5 = 0;
    assign er5 = (count == 11);
    assign rdy5 = ((count >= 1 && count < 3) || (count >= 8 && count < 11));
    assign start5 = (count == 8);

    // Zadatak 6
    assign endd6 = (count == 2);
    assign stop6 = (count == 5);
    assign er6 = (count == 10);
    assign rdy6 = ((count >= 1 && count < 3) || (count >= 4 && count < 7) || (count >= 9 && count < 11));

    // Zadatak 7
    assign endd7 = (count == 3);
    assign start7 = (count == 5);
    assign status_valid7 = (count == 10);
    assign instartsv7 = (count >= 3 && count < 8);

    // Zadatak 8
    assign rt8 = (count >= 0 && count < 3);
    assign enable8 = (count == 7);

    // Zadatak 9
    assign rdy9 = (count >= 2 && count < 8);
    assign start9 = (count >= 5 && count < 8);
    assign interrupt9 = (count == 8);

    // Zadatak 10
    assign ack10 = (count == 6);
    assign req10 = (count == 1);

endmodule

