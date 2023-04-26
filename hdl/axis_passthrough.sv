/**
 * The AXI-Stream pass-through module will accept an AXI-Stream and allow it to
 * be passed-through (or discarded) depending on:
 *  (1) that a request for the 'next' stream is high on first beat
 *  (2) that the connecting AXI-Stream 'master' interface is ready
 *
 * Point (2) is optional and can be turned 'off' by setting the GREEDY
 * parameter to 1.
 *
 * Note: The 'm_tready' is generated via combinatorial logic and not registered
 * before being outputted. For best timing performance, 'slave' stream should
 * use a skid buffer module to feed into this pass-though module.
 */

`default_nettype none

module axis_passthrough
  #(parameter   CFG_DWIDTH  = 8,
    parameter   GREEDY      = 0,
    parameter   AXIS_DWIDTH = 32)
   (input   wire    clk,
    input   wire    rst,

    input   wire    next,

    output  logic   [CFG_DWIDTH-1:0]    count_drop,
    input   wire                        count_clear,

    input   wire    [AXIS_DWIDTH-1:0]   s_tdata,
    input   wire                        s_tlast,
    input   wire                        s_tvalid,
    output  logic                       s_tready,

    output  logic   [AXIS_DWIDTH-1:0]   m_tdata,
    output  logic                       m_tlast,
    output  logic                       m_tvalid,
    input   wire                        m_tready
);

    logic   pending;
    logic   pass;
    logic   pass_locked;

    logic   [AXIS_DWIDTH-1:0]   tdata;
    logic                       tlast;
    logic                       tvalid;
    logic                       tready;

    // waiting for stream to start (pending will be high for first word of
    // stream)
    always_ff @(posedge clk) begin
        if (rst) begin
            pending <= 1'b1;
        end
        else if (s_tvalid & s_tready & s_tlast) begin
            pending <= 1'b1;
        end
        else if (s_tvalid & s_tready) begin
            pending <= 1'b0;
        end
    end

    // pass though or not
    always_comb begin
        pass = (next & pending & tready) | pass_locked;
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            pass_locked <= 1'b0;
        end
        else if (tvalid & tready & tlast) begin
            pass_locked <= 1'b0;
        end
        else if (tvalid & tready) begin
            pass_locked <= 1'b1;
        end
    end

    // count the number of streams dropped
    always_ff @(posedge clk) begin
        if (rst) begin
            count_drop <= '0;
        end
        else if (count_clear) begin
            count_drop <= '0;
        end
        else if (pending & s_tvalid & s_tready & ~pass) begin
            count_drop <= count_drop + 'd1;
        end
    end

    always_comb begin
        tdata       = s_tdata;
        tlast       = s_tlast & pass;
        tvalid      = s_tvalid & pass;

        s_tready    = tready | ~pass;
    end

    axis_skid_buffer #(
        .GREEDY         (GREEDY),
        .AXIS_DWIDTH    (AXIS_DWIDTH))
    axis_skid_buffer_ (
        .clk    (clk),
        .rst    (rst),

        .s_tdata    (tdata),
        .s_tlast    (tlast),
        .s_tvalid   (tvalid),
        .s_tready   (tready),

        .m_tdata    (m_tdata),
        .m_tlast    (m_tlast),
        .m_tvalid   (m_tvalid),
        .m_tready   (m_tready)
    );


`ifdef FORMAL

`ifdef AXIS_PASSTHROUGH
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
    // Check the proper relationship between the inner interface bus signals
    //

    // inner interface path holds data steady when stalled
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(tvalid && ~tready)) begin
            INNER_DATA_STABLE : assert($stable(tdata));
        end
    end

    // inner interface path only has tlast high when tvalid is also high
    always_comb begin
        if (past_exists && tlast) begin
            INNER_LAST_VALID : assert(tvalid);
        end
    end

    // inner interface path will only lower last after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(tlast)) begin
            INNER_LAST_LOWER : assert($past(tvalid && tready));
        end
    end

    // inner interface path will only lower valid after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(tvalid)) begin
            INNER_VALID_LOWER : assert($past(tready));
        end
    end

    // inner interface path will only lower ready after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(tready)) begin
            INNER_READY_LOWER : assert($past(tvalid));
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

`endif
endmodule

`ifdef YOSYS
`default_nettype wire
`endif
