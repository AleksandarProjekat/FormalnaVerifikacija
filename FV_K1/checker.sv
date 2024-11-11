checker black_box_checker (
    clk, reset,
    a1, a2, a3,
    count_a,
    b,
    c1, c2, c3, c4,
    a5, a6,
    b1, b2, b3, b4
);

    default clocking @(posedge clk);
    endclocking

    default disable iff reset;


    // Funkcija za proveru Fibonacijevih brojeva
    function automatic bit is_fibonacci(input logic [10:0] number);
        int a = 0, b = 1, c;
        int extended_number = number; 
        for (int i = 0; i < 20; i++) begin
            if (b == extended_number) return 1;
            c = a + b;
            a = b;
            b = c;
        end
        return 0;
    endfunction


    // Funkcija za proveru savrsenih kvadrata
    function automatic bit is_perfect_square(input logic [10:0] number);
        int extended_number = number; 
        for (int i = 1; i * i <= extended_number; i++) begin
            if (i * i == extended_number) return 1;
        end
        return 0;
    endfunction

    // Signal koji označava da li je count_a Harshad broj iz definisanog skupa
    logic is_harshad_count_a;

    // Funkcija za proveru da li je count_a u skupu Harshad brojeva
    function automatic bit is_hardcoded_harshad(input logic [10:0] number);
        return number == 18 || number == 21 || number == 24;
    endfunction

    // Dodeljivanje vrednosti za Harshad signal is_harshad_count_a
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            is_harshad_count_a <= 0;
        end else begin
            is_harshad_count_a <= is_hardcoded_harshad(count_a);
        end
    end


    // p1: ako je a1 aktivan i count_a je Fibonacijev broj, onda ce a1 biti deaktiviran tri ciklusa kasnije.
    p1: assert property ((a1 && is_fibonacci(count_a)) |-> ##3 !(a1 && is_fibonacci(count_a))[*1]);

    // p2: kada je a2 aktivan (stepen broja 2), c1 aktivira na sledećih 5 ciklusa u nizu
    p2: cover property (a2 |-> c1[*5]);

    // p3: a3 aktivira samo kada je count_a deljiv sa 7 ili 11, ali nije deljiv sa 5
    p3: assume property ((count_a % 7 == 0 || count_a % 11 == 0) && count_a % 5 != 0 |-> a3);

    // p4: b se aktivira kada je ostakak pri deljenju sa 5 jednak broju 2
    p4: assume property (count_a % 5 == 2 |-> b);

    // p5: kada je aktivan a5, sigurno se nece aktivirati c1, c2, ili c3
    p5: assert property (a5 |-> !c1 && !c2 && !c3);

    // p6: b3 aktivira samo kada je count_a Fibonacijev broj, ako pada znamo da b3 nema vrednosti iz skupa Fibonacijevih brojeva
    p6: assert property (b3 == is_fibonacci(count_a));

    // p7: kada se b4 aktivira, is_harshad_count_a mora se aktivirati u sledecem taktu, a b1 ne sme biti aktivan najmanje 4 ciklusa nakon aktivacije b4.
	property p7_property;
	    @(posedge clk) b4 |-> ##1 (is_harshad_count_a && !b1) ##1 !b1 ##1 !b1;
	endproperty

	p7: assert property (p7_property);

   // p8: kada su b4 i b2 jednaki, a zatim se a6 i b1 podudaraju makar jednom u narednih 34 ciklusa
   p8: assume property ((b4 == b2) |-> ##[1:34] (a6 && b1) ##1 (!a6 || !b1)[*0:$]);

    // p9: kada je count_a Harshad broj, c3 i b4 prate naizmeničan obrazac svakih 5 ciklusa
    p9: cover property (is_harshad_count_a |-> (c3 ##5 b4 ##5 c3));

    // p10: kada je count_a kvadrat neparnog broja, c2 aktivira sledeca 4 ciklusa, a zatim c4 na sledecih 3
    p10: cover property (is_perfect_square(count_a) && count_a % 2 == 1 |-> (c2[*4] ##1 c4[*3]));

    

endchecker

