/**
 * The AXI-Stream multi-master module allows for multiple master AXI-Streams to
 * control the back-pressure of a single AXI-Stream slave.
 */

`default_nettype none

module axis_multi_master
  #(parameter   GREEDY      = 0,
    parameter   AXIS_DWIDTH = 32,
    parameter   PORT_NB     = 8)
   (input   wire    clk,
    input   wire    rst,

    input   wire    [AXIS_DWIDTH-1:0]   s_tdata,
    input   wire                        s_tlast,
    input   wire                        s_tvalid,
    output  logic                       s_tready,

    output  logic   [PORT_NB*AXIS_DWIDTH-1:0]   m_tdata,
    output  logic   [PORT_NB-1:0]               m_tlast,
    output  logic   [PORT_NB-1:0]               m_tvalid,
    input   wire    [PORT_NB-1:0]               m_tready
);

    logic   [AXIS_DWIDTH-1:0]   up_tdata;
    logic                       up_tlast;
    logic                       up_tvalid;
    logic                       up_tready;

    logic   [AXIS_DWIDTH-1:0]   dn_tdata [PORT_NB];
    logic   [PORT_NB-1:0]       dn_tlast;
    logic   [PORT_NB-1:0]       dn_tvalid;
    logic   [PORT_NB-1:0]       dn_tready;

    axis_skid_buffer #(
        .GREEDY         (GREEDY),
        .AXIS_DWIDTH    (AXIS_DWIDTH))
    axis_skid_buffer_slave_ (
        .clk    (clk),
        .rst    (rst),

        .s_tdata    (s_tdata),
        .s_tlast    (s_tlast),
        .s_tvalid   (s_tvalid),
        .s_tready   (s_tready),

        .m_tdata    (up_tdata),
        .m_tlast    (up_tlast),
        .m_tvalid   (up_tvalid),
        .m_tready   (up_tready)
    );

    always_comb begin
        up_tready = &(dn_tready);
    end

    genvar x;
    generate
        for (x = 0; x < PORT_NB; x = x + 1) begin : MASTERS_

            always_comb begin
                dn_tdata    [x] = up_tdata;
                dn_tlast    [x] = up_tlast  & up_tready;
                dn_tvalid   [x] = up_tvalid & up_tready;
            end

            axis_skid_buffer #(
                .GREEDY         (GREEDY),
                .AXIS_DWIDTH    (AXIS_DWIDTH))
            axis_skid_buffer_master_ (
                .clk    (clk),
                .rst    (rst),

                .s_tdata    (dn_tdata   [x]),
                .s_tlast    (dn_tlast   [x]),
                .s_tvalid   (dn_tvalid  [x]),
                .s_tready   (dn_tready  [x]),

                .m_tdata    (m_tdata    [x*AXIS_DWIDTH +: AXIS_DWIDTH]),
                .m_tlast    (m_tlast    [x]),
                .m_tvalid   (m_tvalid   [x]),
                .m_tready   (m_tready   [x])
            );
        end
    endgenerate


`ifdef FORMAL

`ifdef AXIS_MULTI_MASTER
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

    genvar y;
    generate
        for (y = 0; y < PORT_NB; y = y + 1) begin : MASTERS_FORMAL_

            //
            // Check the proper relationship between master interface bus signals
            //

            // master interface path holds data steady when stalled
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $past(m_tvalid[y] && ~m_tready[y])) begin
                    assert($stable(m_tdata[y*AXIS_DWIDTH +: AXIS_DWIDTH]));
                end
            end

            // master interface path only has tlast high when tvalid is also high
            always_comb begin
                if (past_exists && m_tlast[y]) begin
                    assert(m_tvalid[y]);
                end
            end

            // master interface path will only lower last after a transaction
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $fell(m_tlast[y])) begin
                    assert($past(m_tvalid[y] && m_tready[y]));
                end
            end

            // master interface path will only lower valid after a transaction
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $fell(m_tvalid[y])) begin
                    assert($past(m_tready[y]));
                end
            end

            // master interface path will only lower ready after a transaction
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $fell(m_tready[y])) begin
                    `ASSUME($past(m_tvalid[y]));
                end
            end
        end
    endgenerate

`endif
endmodule

`ifdef YOSYS
`default_nettype wire
`endif
