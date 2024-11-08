checker black_box_checker (
    clk, rst,
    a1, a2, a3, a4, a5,
    cntA, cntB,
    b1, b2, b3,
    c1, c2, c3, c4, c5, c6,
    d1, d2, d3, d4, d5
);

    default clocking @(posedge clk);
    endclocking

    default disable iff rst;

    parameter int MAX_CNT = 8192;


    // Funkcija za proveru savršenih brojeva (brojevi jednaki zbiru svojih delilaca, npr. 6 = 1 + 2 + 3)
    function automatic bit is_perfect(input int number);
        int sum = 1;
        int i;
        for (i = 2; i * i <= number; i++) begin
            if (number % i == 0) begin
                sum += i;
                if (i != number / i) sum += number / i;
            end
        end
        return (sum == number && number != 1);
    endfunction

    // Funkcija za proveru Haršadovih brojeva (brojevi deljivi sa sumom svojih cifara)
    function automatic bit is_harshad(input int number);
        int sum = 0, temp = number;
        while (temp > 0) begin
            sum += temp % 10;
            temp /= 10;
        end
        return (number % sum == 0);
    endfunction

    // Funkcija za brojanje jedinica u binarnom prikazu broja
    function automatic int count_one_bits(input int number);
        int count = 0;
        int temp = number;
        while (temp > 0) begin
            count += (temp & 1);
            temp >>= 1;
        end
        return count;
    endfunction

    // Funkcija za proveru specifičnih binarnih obrazaca (brojevi koji sadrže obrazac 010101 u binarnom prikazu)
    function automatic bit has_alternating_pattern(input int number);
        return ((number & 63) == 42);  // 42 u binarnom je 010101
    endfunction


    // Property 1: Assert - `a1` aktivan kada je `cntA` savršen broj
    p1: assert property (a1 |-> is_perfect(cntA));

    // Proverava da li je broj palindromski
    function automatic bit is_palindrome(input int number);
        int reversed = 0, temp = number;
        while (temp > 0) begin
            reversed = (reversed * 10) + (temp % 10);
            temp /= 10;
        end
        return (reversed == number);
    endfunction
	
    // Property 2: Cover - `a2` aktivan kada je `cntB` palindrom i `cntA` ima tačno 5 jedinica
    p2: cover property (a2 && is_palindrome(cntB) && count_one_bits(cntA) == 5);

    // Property 3: Assume - `a3` aktivan kada `cntB` ima obrazac 010101 u poslednjih 6 bita
    p3: assume property (a3 |-> has_alternating_pattern(cntB));

    // Property 4: Assert - `a4` aktivan kada XOR između `cntA` i `cntB` daje sve jedinice
    p4: assert property (a4 |-> (cntA xor cntB == 8191));

    // Property 5: Cover - `a5` aktivan kada su svi bitovi `cntA` različiti
    function automatic bit all_bits_different(input int number);
        int seen = 0;
        int temp = number;
        while (temp > 0) begin
            if ((seen & (1 << (temp % 2))) != 0) return 0;
            seen |= (1 << (temp % 2));
            temp /= 2;
        end
        return 1;
    endfunction
	
    // Property 5: Cover - `a5` aktivan kada su svi bitovi `cntA` različiti
    p5: cover property (a5 && all_bits_different(cntA));

    // Property 6: Assume - `b1` aktivan kada cntA ima tačno 6 jedinica i cntB je paran
    p6: assume property (b1 |-> (count_one_bits(cntA) == 6 && cntB % 2 == 0));

    // Property 7: Assert - `b2` aktivan kada cntA i cntB imaju tačno 3 zajedničke jedinice i cntB nije deljiv sa 3
    p7: assert property (b2 |-> (count_one_bits(cntA & cntB) == 3 && cntB % 3 != 0));

    // Property 8: Cover - `c1`, `c2`, i `c3` aktivni kada je cntA Haršadov broj i cntB ima neparan broj jedinica
    p8: cover property (c1 && c2 && c3 && is_harshad(cntA) && (count_one_bits(cntB) % 2 == 1));

    // Property 9: Assume - `c4` i `c5` ostaju aktivni kada su poslednjih 4 bita cntA i cntB jednaki u naredna 4 ciklusa
    p9: assume property (c4 && c5 |=> ##[0:3] ((cntA & 15) == (cntB & 15)));

    // Property 10: Assert - `d1`, `d3`, i `d5` aktivni kada su ispunjeni specifični odnosi između cntA i cntB
    p10: assert property (d1 && d3 && d5 |-> ((cntA + cntB) % 256 == 0 || (cntA ^ cntB) % 128 == 0 || cntA == cntB / 2));

    // Dodatna propertiji za kreativnost
    // Property 11: Assert - `b3` aktivan kada cntA i cntB imaju isti broj jedinica
    p11: assert property (b3 |-> (count_one_bits(cntA) == count_one_bits(cntB)));

    // Property 12: Cover - `c6` aktivan kada je broj jedinica u cntA veći od 6 ili cntB veći od 6
    p12: cover property (c6 && (count_one_bits(cntA) > 6 || count_one_bits(cntB) > 6));

    // Property 13: Assume - `d2` aktivan kada je broj jedinica u (cntA or cntB) tačno 9
    p13: assume property (d2 |-> (count_one_bits(cntA | cntB) == 9));

    // Dodatni pokrivači za opsege cntA i cntB
    cover_low: cover property ((cntA < MAX_CNT / 3) && (cntB < MAX_CNT / 3));
    cover_mid: cover property ((cntA >= MAX_CNT / 3 && cntA < (2 * MAX_CNT / 3)) && (cntB >= MAX_CNT / 3 && cntB < (2 * MAX_CNT / 3)));
    cover_high: cover property ((cntA >= (2 * MAX_CNT / 3)) && (cntB >= (2 * MAX_CNT / 3)));

endchecker
