library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

entity black_box is
    Port (
        clk, rst : in std_logic;
        a1, a2, a3, a4, a5 : out std_logic;           -- Razni izlazi bazirani na složenim uslovima
        cntA : inout integer range 0 to 8191;         -- Ulazno-izlazni brojač cntA sa proširenim opsegom
        cntB : inout integer range 0 to 8191;         -- Ulazno-izlazni brojač cntB sa specifičnim matematičkim pravilima
        b1, b2, b3 : out std_logic;                   -- b1, b2, b3 izlazi sa specifičnim pravilima
        c1, c2, c3, c4, c5, c6 : out std_logic;       -- Izlazi c1-c6 koji reaguju na različite uslove vezane za cntA i cntB
        d1, d2, d3, d4, d5 : out std_logic            -- d1-d5 aktivni u specifičnim kombinacijama i opsezima cntA i cntB
    );
end black_box;

architecture Behavioral of black_box is
    signal cnt : integer range 0 to 8191;

    -- Funkcija za brojanje jedinica u binarnom prikazu broja
    function count_one_bits(number: integer) return integer is
        variable count : integer := 0;
        variable temp : integer := number;
    begin
        while temp > 0 loop
            count := count + (temp mod 2);
            temp := temp / 2;
        end loop;
        return count;
    end function;

begin
    -- Proces za cntA i cntB pri svakom taktu
    process(clk, rst)
    begin
        if rst = '1' then
            cnt <= 0;
            cntA <= 0;         -- Resetuje cntA na početnu vrednost
            cntB <= 5;         -- Resetuje cntB na početnu vrednost
        elsif rising_edge(clk) then
            cnt <= cnt + 1;
            cntA <= (cntA + 10) mod 8192;       -- cntA se povećava za 10 i kruži unutar opsega 0-8191
            cntB <= (cntB + 15) mod 8192;       -- cntB se povećava za 15 i kruži unutar opsega 0-8191
        end if;
    end process;

    -- Signal a1 menja stanje kada je cntA u opsegu od 0 do 1024 ili od 4096 do 8191
    a1 <= '1' when (cntA < 1024 or cntA > 4096) else '0';

    -- Signal a2 menja stanje kada je cntB u opsegu od 500 do 2500
    a2 <= '1' when (cntB > 500 and cntB < 2500) else '0';

    -- Signal a3 menja stanje kada cntB ima obrazac 010101 u poslednjih 6 bita
    a3 <= '1' when ((cntB and 63) = 42) else '0';

    -- Signal a4 menja stanje kada XOR između cntA i cntB daje vrednost sa svim jedinicama u opsegu 11-bitnog broja
    a4 <= '1' when (cntA xor cntB = 2047) else '0';

    -- Signal a5 menja stanje kada su svi bitovi cntA različiti (u okviru nižih 4 bita)
    a5 <= '1' when (cntA and 15) = 1 or (cntA and 15) = 2 or (cntA and 15) = 4 or (cntA and 15) = 8 else '0';

    -- Signal b1 aktivan kada cntA ima tačno 5 jedinica
    b1 <= '1' when count_one_bits(cntA) = 5 else '0';

    -- Signal b2 aktivan kada cntA i cntB imaju 3 zajedničke jedinice
    b2 <= '1' when count_one_bits(cntA and cntB) = 3 else '0';

    -- Signal b3 aktivan kada cntA i cntB imaju jednak broj jedinica
    b3 <= '1' when count_one_bits(cntA) = count_one_bits(cntB) else '0';

    -- Signali c1-c6 bazirani na različitim logičkim pravilima između cntA i cntB
    c1 <= '1' when cntA < 2000 else '0';
    c2 <= '1' when cntA > 6000 else '0';
    c3 <= '1' when cntA = cntB else '0';
    c4 <= '1' when (cntA mod 256 = cntB mod 256) else '0';
    c5 <= '1' when (cntA and cntB) = 16#55AA# else '0';
    c6 <= '1' when count_one_bits(cntA or cntB) > 6 else '0';

    -- Signali d1-d5 aktivni u specifičnim uslovima između cntA i cntB
    d1 <= '1' when (cntA + cntB) mod 256 = 0 else '0';
    d2 <= '1' when count_one_bits(cntA or cntB) = 9 else '0';
    d3 <= '1' when cntA mod 256 = cntB mod 256 else '0';
    d4 <= '1' when (cntA xor cntB) = 16#AAA# else '0';
    d5 <= '1' when cntA = cntB / 2 or cntB = cntA / 2 else '0';

end Behavioral;
