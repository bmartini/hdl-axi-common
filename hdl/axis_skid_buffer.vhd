-- The AXI-Stream skid buffer module registers the ready signal and compensates
-- for the delay using by using a diversion 'skid' register.

library ieee;
  use ieee.std_logic_1164.all;
  use ieee.numeric_std.all;

entity axis_skid_buffer is
  generic (
    greedy      : integer := 0;
    axis_dwidth : integer := 32
  );
  port (
    clk      : in    std_logic;
    rst      : in    std_logic;
    s_tdata  : in    unsigned(axis_dwidth - 1 downto 0);
    s_tlast  : in    std_logic;
    s_tready : out   std_logic;
    s_tvalid : in    std_logic;
    m_tdata  : out   unsigned(axis_dwidth - 1 downto 0);
    m_tlast  : out   std_logic;
    m_tready : in    std_logic;
    m_tvalid : out   std_logic
  );
end entity axis_skid_buffer;

architecture rtl of axis_skid_buffer is

  signal skid_tdata  : unsigned(axis_dwidth - 1 downto 0);
  signal skid_tlast  : std_logic;
  signal skid_tvalid : std_logic;
  signal s_tdata_i   : unsigned(axis_dwidth - 1 downto 0);
  signal s_tlast_i   : std_logic;
  signal s_tvalid_i  : std_logic;
  signal m_active    : std_logic;

begin

  -- Skid register for master data value. The 'skid_tdata' variable will store
  -- the data value that was (or would have been) written on the master
  -- tdata output if the interface was 'ready'.
  skid_data : process (clk) is
  begin

    if rising_edge(clk) then
      skid_tdata <= s_tdata_i;
    end if;

  end process skid_data;

  -- Skid register for master valid flag. The 'skid_tvalid' variable will
  -- indicate when high that there is a pending 'valid' entry in the skid
  -- buffers that have not been consumed by down stream.
  skid_control : process (clk) is
  begin

    if rising_edge(clk) then
      if (rst = '1') then
        skid_tlast  <= '0';
        skid_tvalid <= '0';
      else
        skid_tlast  <= s_tlast_i and (not m_active);
        skid_tvalid <= s_tvalid_i and (not m_active);
      end if;
    end if;

  end process skid_control;

  -- skid mux: if 's_tready' is lowered the previous master values that have
  -- not been passed to the downstream pipeline will be held in the skid
  -- registers until they can be re-sent.
  intermediate_slave : process (s_tdata, s_tlast, s_tvalid, s_tready,
                                skid_tdata, skid_tlast, skid_tvalid) is
  begin

    if (s_tready = '1') then
      s_tdata_i <= s_tdata;
    else
      s_tdata_i <= skid_tdata;
    end if;

    if (s_tready = '1') then
      s_tlast_i <= s_tlast;
    else
      s_tlast_i <= skid_tlast;
    end if;

    if (s_tready = '1') then
      s_tvalid_i <= s_tvalid;
    else
      s_tvalid_i <= skid_tvalid;
    end if;

  end process intermediate_slave;

  -- when 'master' stream is ready or 'slave' stream has valid data, set
  -- 'slave' ready to high if the modules 'master' pipeline is not stalled

  slave_ready_generation : if (greedy = 0) generate

    slave_ready_strict : process (clk) is
    begin

      if rising_edge(clk) then
        if (rst = '1') then
          s_tready <= '0';
        else
          if ((m_tready or s_tvalid) = '1') then
            s_tready <= m_active;
          end if;
        end if;
      end if;

    end process slave_ready_strict;

  else generate

    slave_ready_greedy : process (clk) is
    begin

      if rising_edge(clk) then
        if (rst = '1') then
          s_tready <= '0';
        else
          if ((m_active or s_tvalid) = '1') then
            s_tready <= m_active;
          end if;
        end if;
      end if;

    end process slave_ready_greedy;

  end generate slave_ready_generation;

  master_data : process (clk) is
  begin

    if rising_edge(clk) then
      if (m_active = '1') then
        m_tdata <= s_tdata_i;
      end if;
    end if;

  end process master_data;

  master_control : process (clk) is
  begin

    if rising_edge(clk) then
      if (rst = '1') then
        m_tlast  <= '0';
        m_tvalid <= '0';
      else
        if (m_active = '1') then
          m_tlast  <= s_tlast_i;
          m_tvalid <= s_tvalid_i;
        end if;
      end if;
    end if;

  end process master_control;

  -- Pipiline is active when empty or when master interface is ready.
  master_active : process (m_tvalid, m_tready) is
  begin

    m_active <= (not m_tvalid) or m_tready;

  end process master_active;

end architecture axis_skid_buffer;
