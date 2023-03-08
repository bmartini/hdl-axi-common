/**
 * The AXI-Stream Gear Box will serializes or deserializes a stream of data
 * depending of the relative widths of the streams. It is only one register
 * deep but does also register the ready flag and thus has implemented a skid
 * buffer.
 *
 * Serializes the 'slave' data word into multiple smaller 'master' data words.
 * The module will stall when the 'm_tready' flag deasserts.
 *
 * Deserializes multiple 'slave' flow bus data words into a single, larger
 * 'master' data words. Arranges them first to the right and moving left. If
 * there is a pause in the incoming 'slave' stream the values already written
 * into the larger 'master' word will stay until enough 'slave' data has been
 * sent in to complete the 'master' word unless a 's_tlast' signal forces the
 * master transfer. The module will stall when the 'm_tready' flag deasserts.
 */

`default_nettype none

module axis_gearbox
  #(parameter   GREEDY      = 0,
    parameter   S_DWIDTH    = 2,
    parameter   M_DWIDTH    = 8)
   (input   wire    clk,
    input   wire    rst,

    input   wire    [S_DWIDTH-1:0]  s_tdata,
    input   wire                    s_tlast,
    input   wire                    s_tvalid,
    output  logic                   s_tready,

    output  logic   [M_DWIDTH-1:0]  m_tdata,
    output  logic                   m_tlast,
    output  logic                   m_tvalid,
    input   wire                    m_tready
);

    logic   [S_DWIDTH-1:0]  skid_tdata;
    logic                   skid_tlast;
    logic                   skid_tvalid;

    logic   [S_DWIDTH-1:0]  s_tdata_i;
    logic                   s_tlast_i;
    logic                   s_tvalid_i;
    logic                   m_active;

    // Skid register for master data value. The 'skid_tdata' variable will
    // store the data value that was (or would have been) written on the master
    // tdata output if the interface was 'ready'.
    always_ff @(posedge clk) begin
        skid_tdata <= s_tdata_i;
    end

    // Skid register for master valid flag. The 'skid_tvalid' variable will
    // indicate when high that there is a pending 'valid' entry in the skid
    // buffers that have not been consumed by down stream.
    always_ff @(posedge clk) begin
        if (rst) begin
            skid_tlast  <= 1'b0;
            skid_tvalid <= 1'b0;
        end
        else begin
            skid_tlast  <= s_tlast_i    & ~m_active;
            skid_tvalid <= s_tvalid_i   & ~m_active;
        end
    end

    // skid mux: if 's_tready' is lowered the previous master values that have
    // not been passed to the downstream pipeline will be held in the skid
    // registers until they can be re-sent.
    always_comb begin
        s_tdata_i   = s_tready ? s_tdata    : skid_tdata;
        s_tlast_i   = s_tready ? s_tlast    : skid_tlast;
        s_tvalid_i  = s_tready ? s_tvalid   : skid_tvalid;
    end

    // Pipeline is active when empty or when master interface is ready.
    always_comb begin
        m_active = ~m_tvalid | m_tready;
    end


`ifdef FORMAL

`ifdef AXIS_GEARBOX
    `define ASSUME assume
`else
    `define ASSUME assert
`endif

    logic   past_exists;
    initial begin
        past_exists = 1'b0;

        // ensure reset is triggered at the start
        restrict property (rst == 1'b1);
    end

    always_ff @(posedge clk) begin
        past_exists <= 1'b1;
    end

    //
    // Check the proper relationship between slave interface bus signals
    //

    // slave interface path holds data steady when stalled
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(s_tvalid && ~s_tready)) begin
            S_DATA_STABLE : `ASSUME($stable(s_tdata));
        end
    end

    // slave interface path only has tlast high when tvalid is also high
    always_comb begin
        if (past_exists && s_tlast) begin
            S_LAST_VALID : `ASSUME(s_tvalid);
        end
    end

    // slave interface path will only lower last after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(s_tlast)) begin
            S_LAST_LOWER : `ASSUME($past(s_tvalid && s_tready));
        end
    end

    // slave interface path will only lower valid after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(s_tvalid)) begin
            S_VALID_LOWER : `ASSUME($past(s_tready));
        end
    end

    // slave interface path will only lower ready after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(s_tready)) begin
            S_READY_LOWER : assert($past(s_tvalid));
        end
    end

    //
    // Check the proper relationship between master interface bus signals
    //

    // master interface path holds data steady when stalled
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(m_tvalid && ~m_tready)) begin
            M_DATA_STABLE : assert($stable(m_tdata));
        end
    end

    // master interface path only has tlast high when tvalid is also high
    always_comb begin
        if (past_exists && m_tlast) begin
            M_LAST_VALID : assert(m_tvalid);
        end
    end

    // master interface path will only lower last after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(m_tlast)) begin
            M_LAST_LOWER : assert($past(m_tvalid && m_tready));
        end
    end

    // master interface path will only lower valid after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(m_tvalid)) begin
            M_VALID_LOWER : assert($past(m_tready));
        end
    end

    // master interface path will only lower ready after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(m_tready)) begin
            M_READY_LOWER : `ASSUME($past(m_tvalid));
        end
    end

    //
    // Check the proper relationship with skid logic
    //

    // skid logic holds data steady when back pressure is being applied
    always_ff @(posedge clk) begin
        if (past_exists && $past(~s_tready)) begin
            SKID_DATA_STABLE : assert($stable(skid_tdata));
        end
    end

    // skid logic holds last slave data value when back pressure is applied
    always_ff @(posedge clk) begin
        if (past_exists && $fell(s_tready)) begin
            SKID_DATA_UPDATE : assert(skid_tdata == $past(s_tdata));
        end
    end

    // skid tlast should be high only when skid tvalid is high
    always_comb begin
        if (past_exists && skid_tlast) begin
            SKID_LAST_VALID : assert(skid_tvalid);
        end
    end

    // skid logic holds control signals steady when back pressure is being applied
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $stable(~s_tready)) begin
            SKID_LAST_STABLE : assert($stable(skid_tlast));
            SKID_VALID_STABLE : assert($stable(skid_tvalid));
        end
    end

`endif


    generate
        if (S_DWIDTH == M_DWIDTH) begin : PASS_

            // when 'master' stream is ready or 'slave' stream has valid data,
            // set 'slave' ready to high if the modules 'master' pipeline is
            // not stalled
            if (GREEDY == 0) begin : STRICT_

                always_ff @(posedge clk) begin
                    if      (rst)                   s_tready <= 1'b0;
                    else if (m_tready | s_tvalid)   s_tready <= m_active;
                end

            end
            else begin : GREEDY_

                always_ff @(posedge clk) begin
                    if      (rst)                   s_tready <= 1'b0;
                    else if (m_active | s_tvalid)   s_tready <= m_active;
                end

            end

            always_ff @(posedge clk) begin
                if (m_active) begin
                    m_tdata <= s_tdata_i;
                end
            end

            always_ff @(posedge clk) begin
                if (rst) begin
                    m_tlast     <= 1'b0;
                    m_tvalid    <= 1'b0;
                end
                else if (m_active) begin
                    m_tlast     <= s_tlast_i;
                    m_tvalid    <= s_tvalid_i;
                end
            end

`ifdef FORMAL
            //
            // Check that the master data is sourced from correct locations
            //

            // master data sourced from slave data
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $past(m_tready && s_tready)) begin
                    M_FROM_S_UPDATE : assert(m_tdata == $past(s_tdata));
                end
            end

            // master data sourced from skid data
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $past(m_tready && ~s_tready)) begin
                    M_FROM_SKID_UPDATE : assert(m_tdata == $past(skid_tdata));
                end
            end
`endif
        end
        else if (S_DWIDTH > M_DWIDTH) begin : SERIAL_

            localparam DATA_NB = S_DWIDTH / M_DWIDTH;

            logic   [2*DATA_NB-1:0] token_nx;
            logic   [DATA_NB-1:0]   token;

            logic   [S_DWIDTH-1:0]  serial_data;
            logic   [DATA_NB-1:0]   serial_last;
            logic   [DATA_NB-1:0]   serial_valid;
            logic                   s_active;
            logic                   s_tready_i;

            always_comb begin
                s_active    = s_tvalid_i & token[0];
                s_tready    = s_tready_i & token[0];
            end

            // set 'slave' stream ready to high if the modules 'master'
            // pipeline is not stalled and the serial data if available to be
            // written to
            if (GREEDY == 0) begin : STRICT_

                always_ff @(posedge clk) begin
                    if      (rst)                               s_tready_i <= 1'b0;
                    else if ((m_tready & token[0]) | s_tvalid)  s_tready_i <= m_active;
                end

            end
            else begin : GREEDY_

                always_ff @(posedge clk) begin
                    if      (rst)                               s_tready_i <= 1'b0;
                    else if ((m_active & token[0]) | s_tvalid)  s_tready_i <= m_active;
                end

            end

            always_comb begin
                token_nx = {token, token};
            end

            always_ff @(posedge clk) begin
                if (rst) token <= 'b1;
                else if (m_active) begin

                    if ( ~token[0] | s_active) begin
                        token <= token_nx[DATA_NB-1 +: DATA_NB];
                    end
                end
            end

            always_ff @(posedge clk) begin
                if (m_active) begin

                    serial_data <= serial_data >> M_DWIDTH;
                    if (s_active) begin
                        serial_data <= s_tdata_i;
                    end
                end
            end

            always_ff @(posedge clk) begin
                if (rst) serial_last <= 'b0;
                else if (m_active) begin

                    serial_last <= serial_last >> 1;
                    if (s_active & s_tlast_i) begin
                        serial_last             <= 'b0;
                        serial_last[DATA_NB-1]  <= 1'b1;
                    end
                end
            end

            always_ff @(posedge clk) begin
                if (rst) serial_valid <= 'b0;
                else if (m_active) begin

                    serial_valid <= serial_valid >> 1;
                    if (s_active) begin
                        serial_valid <= {DATA_NB{1'b1}};
                    end
                end
            end

            always_comb begin
                m_tdata  = serial_data  [0 +: M_DWIDTH];
                m_tlast  = serial_last  [0];
                m_tvalid = serial_valid [0];
            end

`ifdef FORMAL
            logic   [S_DWIDTH-1:0]  s_tdata_a;
            logic   [S_DWIDTH-1:0]  s_tdata_b;
            logic   [S_DWIDTH-1:0]  s_current;
            logic   [M_DWIDTH-1:0]  s_str [DATA_NB];
            logic                   s_wr;
            logic                   s_rd;
            logic                   cnt_done;
            integer                 cnt;

            initial begin
                rst = 1'b1;
            end

            function logic last_valid(
                input   logic   [DATA_NB-1:0]   last,
                input   logic   [DATA_NB-1:0]   valid
            );
                integer i;

                begin
                    last_valid = 1'b1;

                    for (i = 0; i < DATA_NB; i = i + 1) begin
                        if (last[i] & ~valid[i]) begin
                            last_valid = 1'b0;
                        end
                    end
                end
            endfunction

            initial begin
                assume(last_valid(serial_last, serial_valid));
            end

            always_comb begin
                SERIAL_LAST_VALID : assert(last_valid(serial_last, serial_valid));
            end

            // ping pong buffer to capture the slave data currently being sent
            // master stream and any that is being stored in the skid buffer
            always_ff @(posedge clk) begin
                if      (rst)                   s_wr <= 1'b0;
                else if (s_tvalid & s_tready)   s_wr <= ~s_wr;
            end

            always_ff @(posedge clk) begin
                if      (rst)       s_rd <= 1'b0;
                else if (cnt_done)  s_rd <= ~s_rd;
            end

            always_ff @(posedge clk) begin
                if (s_tvalid & s_tready & ~s_wr) s_tdata_a <= s_tdata;
            end

            always_ff @(posedge clk) begin
                if (s_tvalid & s_tready &  s_wr) s_tdata_b <= s_tdata;
            end

            always_ff @(posedge clk) begin
                if (s_rd)   s_current <= s_tdata_b;
                else        s_current <= s_tdata_a;
            end

            genvar xx;
            for (xx = 0; xx < DATA_NB; xx = xx + 1) begin

                always_comb begin
                    s_str[xx] = s_current[xx*M_DWIDTH +: M_DWIDTH];
                end

            end

            // counts out the master stream data as a position within the slave
            // stream word, use that position to compare the m_tdata with is
            // corresponding slice of the s_tdata word
            always_ff @(posedge clk) begin
                if (rst) begin
                    cnt         <=  'b0;
                    cnt_done    <= 1'b0;
                end
                else begin
                    cnt_done    <= 1'b0;

                    if (m_tvalid & m_tready) begin
                        cnt <= cnt + 'd1;

                        if (cnt >= (DATA_NB-1)) begin
                            cnt         <= 'b0;
                            cnt_done    <= 1'b1;
                        end
                    end
                end
            end

            always_ff @(posedge clk) begin
                if (past_exists && $past(~rst) && $past(~rst, 2) && $past((m_tvalid & m_tready), 2)) begin
                    SOURCE_M_FROM_STREAM : assert($past(m_tdata, 2) == s_str[$past(cnt, 2)]);
                end
            end

`endif
        end
        else if (S_DWIDTH < M_DWIDTH) begin : DSERIAL_

            localparam DATA_NB = M_DWIDTH/S_DWIDTH;

            integer                 ii;
            logic   [2*DATA_NB-1:0] token_nx;
            logic   [DATA_NB-1:0]   token;

            // when master stream is ready or slave stream has valid data, set
            // upstream ready to high if the modules 'master' pipeline is not
            // stalled
            always_ff @(posedge clk) begin
                if      (rst)                   s_tready <= 1'b0;
                else if (m_tvalid | s_tready)   s_tready <= m_active;
            end

            always_comb begin
                token_nx = {token, token};
            end

            always_ff @(posedge clk) begin
                if (rst) m_tlast <= 1'b0;
                else if (m_active) begin
                    m_tlast <= s_tvalid_i & s_tlast_i;
                end
            end

            always_ff @(posedge clk) begin
                if (rst) m_tvalid <= 1'b0;
                else if (m_active) begin
                    m_tvalid <= (token[DATA_NB-1] & s_tvalid_i) | (s_tvalid_i & s_tlast_i);
                end
            end

            always_ff @(posedge clk) begin
                if (rst | (m_active & s_tvalid_i & s_tlast_i)) begin
                    token <= 'b1;
                end
                else if (m_active & s_tvalid_i) begin
                    token <= token_nx[DATA_NB-1 +: DATA_NB];
                end
            end

            always_ff @(posedge clk) begin
                for (ii=0; ii<DATA_NB; ii=ii+1) begin
                    if (m_active & token[0]) begin
                        m_tdata[ii*S_DWIDTH +: S_DWIDTH] <= {S_DWIDTH{1'b0}};
                    end

                    if (m_active & token[ii]) begin
                        m_tdata[ii*S_DWIDTH +: S_DWIDTH] <= s_tdata_i;
                    end
                end
            end

`ifdef FORMAL
            logic   [M_DWIDTH-1:0]  s_tdata_1p;
            logic   [M_DWIDTH-1:0]  s_tdata_2p;
            logic                   cnt_done;
            integer                 cnt;

            initial begin
                rst = 1'b1;
            end

            // counts out the slave stream data as a position within the master
            // stream word, use that position to compare the s_tdata with is
            // corresponding slice of the m_tdata word
            always_ff @(posedge clk) begin
                if (rst) begin
                    cnt         <=  'b0;
                    cnt_done    <= 1'b0;
                end
                else begin
                    cnt_done    <= 1'b0;

                    if (s_tvalid & s_tready) begin
                        cnt <= cnt + 'd1;

                        if ((cnt >= (DATA_NB-1)) || s_tlast) begin
                            cnt         <= 'b0;
                            cnt_done    <= 1'b1;
                        end
                    end
                end
            end

            always_ff @(posedge clk) begin
                if (s_tvalid & s_tready) begin
                    if (cnt == 0) begin
                        s_tdata_1p <= {M_DWIDTH{1'b0}};
                    end

                    s_tdata_1p[cnt*S_DWIDTH +: S_DWIDTH] <= s_tdata;
                end
            end

            always_ff @(posedge clk) begin
                if (cnt_done) begin
                    s_tdata_2p  <= s_tdata_1p;
                end
            end

            always_ff @(posedge clk) begin
                if (past_exists && $past(~rst & m_tvalid & m_tready)) begin
                    assert($past(m_tdata) == s_tdata_2p);
                end
            end

`endif

        end
    endgenerate

endmodule

`ifndef YOSYS
`default_nettype wire
`endif
