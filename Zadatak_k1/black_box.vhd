library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity black_box is
    Port ( 
        clk, reset : in std_logic;
        
        a1, a2, a3 : out std_logic;
        count_a : inout integer range 0 to 2047;
        b : out std_logic;
        
        c1, c2, c3, c4 : out std_logic;
        
        a5, a6 : out std_logic;
        
        b1, b2, b3, b4 : out std_logic
    );
end black_box;

architecture Behavioral of black_box is
    signal count : integer range 0 to 34;

begin
    counter: process(clk, reset)
    begin
        if (reset = '1') then
            count <= 0;
            count_a <= 0;

        elsif (rising_edge(clk)) then
            count <= count + 1;
            count_a <= count_a + 1;
        end if;
    end process;

    -- aktivira se za određeni Fibonacijev niz
    a1 <= '1' when count = 1 or count = 4 or count = 7 or count = 11 or count = 18 or
                     count = 29 else '0';

    -- aktivira se za stepen broja 2
    a2 <= '1' when count = 1 or count = 2 or count = 4 or count = 8 or count = 16 or 
                     count = 32 else '0';

    -- aktivira se kada je count deljiv sa 7 ili 11, ali nije deljiv sa 5
    a3 <= '1' when ((count mod 7 = 0) or (count mod 11 = 0)) and (count mod 5 /= 0) else '0';

    -- aktivira se za brojeve sa ostatkom 2 kada se dele sa 5
    b <= '1' when (count mod 5 = 2) else '0';

    c1 <= '1' when count = 3 or count = 7 or count = 11 or count = 13 or count = 17 else '0';
    c2 <= '1' when count = 5 or count = 9 or count = 15 or count = 19 or count = 23 else '0';
    c3 <= '1' when count = 8 or count = 16 or count = 24 or count = 32 else '0';
    c4 <= '1' when count >= 10 and count <= 20 else '0';

    -- signali a5, a6 koriste aktivaciju na osnovu opsega
    a5 <= '1' when count > 24  and count <= 34 else '0';
    a6 <= '0' when (count < 12) or (count > 22) else '1';

    -- signali koriste nasumicne obrasce
    b1 <= '1' when count = 11 or count = 34 else '0';
    b2 <= '1' when count = 9 or count = 18 else '0';
    b3 <= '1' when count = 10 or count = 20 else '0';

    -- Aktivacija signala b4 kada je count neki od Harsadovih brojeva
    b4 <= '1' when  count = 18 or count = 21 or count = 24  else '0';


end Behavioral;

