module panex #(parameter S = 5) // S = broj diskova svake boje
    (
        input clk,
        input rst,
        input [1:0] fr,  // Izvorni stub (00 - levi, 01 - srednji, 10 - desni)
        input [1:0] to   // Ciljni stub
    );

    // Definicija registara za šipke, po jedan za svaku boju
    logic [S-1:0] left_red, mid_red, right_red;    // Diskovi crvene boje
    logic [S-1:0] left_blue, mid_blue, right_blue; // Diskovi plave boje

    always @(posedge clk) begin
        if (rst) begin
            // Reset: svi crveni diskovi na levom stubu, plavi na desnom
            left_red   <= '1;  // Svi crveni diskovi na levom stubu
            mid_red    <= '0;
            right_red  <= '0;

            left_blue  <= '0;
            mid_blue   <= '0;
            right_blue <= '1;  // Svi plavi diskovi na desnom stubu
        end else begin
            // Pravila za pomeranje crvenih diskova
            if (fr == 2'b00 && to == 2'b01) begin  // Levi → Srednji
                if (left_red > mid_red) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (left_red[i]) begin
                            left_red[i]  <= 1'b0;
                            mid_red[i]   <= 1'b1;
                            break;
                        end
                    end
                end
            end
            if (fr == 2'b00 && to == 2'b10) begin  // Levi → Desni
                if (left_red > right_red) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (left_red[i]) begin
                            left_red[i]  <= 1'b0;
                            right_red[i] <= 1'b1;
                            break;
                        end
                    end
                end
            end
            if (fr == 2'b01 && to == 2'b00) begin  // Srednji → Levi
                if (mid_red > left_red) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (mid_red[i]) begin
                            mid_red[i]  <= 1'b0;
                            left_red[i] <= 1'b1;
                            break;
                        end
                    end
                end
            end
            if (fr == 2'b01 && to == 2'b10) begin  // Srednji → Desni
                if (mid_red > right_red) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (mid_red[i]) begin
                            mid_red[i]  <= 1'b0;
                            right_red[i] <= 1'b1;
                            break;
                        end
                    end
                end
            end
            if (fr == 2'b10 && to == 2'b00) begin  // Desni → Levi
                if (right_red > left_red) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (right_red[i]) begin
                            right_red[i] <= 1'b0;
                            left_red[i]  <= 1'b1;
                            break;
                        end
                    end
                end
            end
            if (fr == 2'b10 && to == 2'b01) begin  // Desni → Srednji
                if (right_red > mid_red) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (right_red[i]) begin
                            right_red[i] <= 1'b0;
                            mid_red[i]   <= 1'b1;
                            break;
                        end
                    end
                end
            end

            // Pravila za pomeranje plavih diskova
            if (fr == 2'b00 && to == 2'b01) begin  // Levi → Srednji
                if (left_blue > mid_blue) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (left_blue[i]) begin
                            left_blue[i]  <= 1'b0;
                            mid_blue[i]   <= 1'b1;
                            break;
                        end
                    end
                end
            end
            if (fr == 2'b00 && to == 2'b10) begin  // Levi → Desni
                if (left_blue > right_blue) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (left_blue[i]) begin
                            left_blue[i]  <= 1'b0;
                            right_blue[i] <= 1'b1;
                            break;
                        end
                    end
                end
            end
            if (fr == 2'b01 && to == 2'b00) begin  // Srednji → Levi
                if (mid_blue > left_blue) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (mid_blue[i]) begin
                            mid_blue[i]  <= 1'b0;
                            left_blue[i] <= 1'b1;
                            break;
                        end
                    end
                end
            end
            if (fr == 2'b01 && to == 2'b10) begin  // Srednji → Desni
                if (mid_blue > right_blue) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (mid_blue[i]) begin
                            mid_blue[i]  <= 1'b0;
                            right_blue[i] <= 1'b1;
                            break;
                        end
                    end
                end
            end
            if (fr == 2'b10 && to == 2'b00) begin  // Desni → Levi
                if (right_blue > left_blue) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (right_blue[i]) begin
                            right_blue[i] <= 1'b0;
                            left_blue[i]  <= 1'b1;
                            break;
                        end
                    end
                end
            end
            if (fr == 2'b10 && to == 2'b01) begin  // Desni → Srednji
                if (right_blue > mid_blue) begin
                    for (int i = S-1; i >= 0; i--) begin
                        if (right_blue[i]) begin
                            right_blue[i] <= 1'b0;
                            mid_blue[i]   <= 1'b1;
                            break;
                        end
                    end
                end
            end
        end
    end

    // Pravila za validaciju poteza
    assume_no_invalid_moves: assume property(@(posedge clk) !(fr == to)); // Zabranjeno kretanje u isti stub
    assume_valid_source: assume property(@(posedge clk) !(fr == 2'b11 || to == 2'b11)); // Nevažeći stubovi

    // Pokrivenost za konačno stanje
    final_cover_red: cover property(@(posedge clk) right_red == '1); // Svi crveni diskovi na desnom stubu
    final_cover_blue: cover property(@(posedge clk) left_blue == '1); // Svi plavi diskovi na levom stubu

endmodule

