/**
 * The AXI-Stream Gear Train will serializes or deserializes a stream of data
 * depending of the relative widths of the streams. Allows for conversion even
 * when slave/master are not multiples of each other. This is possible by
 * connecting two gear boxes back to back with a transfer data sized as the
 * lowest common multiple.
 *
 * Deserializes multiple 'slave' flow bus data words into a single, larger
 * 'master' data words. Arranges them first to the right and moving left. If
 * there is a pause in the incoming 'slave' stream the values already written
 * into the larger 'master' word will stay until enough 'slave' data has been
 * sent in to complete the 'master' word unless a 's_tlast' signal forces the
 * master transfer. The module will stall when the 'm_tready' flag deasserts.
 */

`default_nettype none

module axis_geartrain
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

    // calculate the lowest common multiple
    function automatic integer lcm (
        input integer a,
        input integer b
    );
        integer max, min, multiple;

        multiple = 1;
        max = (a > b) ? a : b;
        min = (a > b) ? b : a;

        while (max * multiple % min != 0) begin
            multiple = multiple + 1;
        end

        lcm = max * multiple;
    endfunction

    localparam TRANSFER_DATA = lcm(S_DWIDTH, M_DWIDTH);

    logic   [TRANSFER_DATA-1:0] t_tdata;
    logic                       t_tlast;
    logic                       t_tvalid;
    logic                       t_tready;

    axis_gearbox #(
        .GREEDY     (GREEDY),
        .S_DWIDTH   (S_DWIDTH),
        .M_DWIDTH   (TRANSFER_DATA))
    axis_gearbox_slave_ (
        .clk        (clk),
        .rst        (rst),

        .s_tdata    (s_tdata),
        .s_tlast    (s_tlast),
        .s_tvalid   (s_tvalid),
        .s_tready   (s_tready),

        .m_tdata    (t_tdata),
        .m_tlast    (t_tlast),
        .m_tvalid   (t_tvalid),
        .m_tready   (t_tready)
    );

    axis_gearbox #(
        .GREEDY     (GREEDY),
        .S_DWIDTH   (TRANSFER_DATA),
        .M_DWIDTH   (M_DWIDTH))
    axis_gearbox_master_ (
        .clk        (clk),
        .rst        (rst),

        .s_tdata    (t_tdata),
        .s_tlast    (t_tlast),
        .s_tvalid   (t_tvalid),
        .s_tready   (t_tready),

        .m_tdata    (m_tdata),
        .m_tlast    (m_tlast),
        .m_tvalid   (m_tvalid),
        .m_tready   (m_tready)
    );


`ifdef FORMAL

`ifdef AXIS_GEARTRAIN
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
    // Check the proper relationship between transferinterface bus signals
    //

    // transfer interface path holds data steady when stalled
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(t_tvalid && ~t_tready)) begin
            T_DATA_STABLE : assert($stable(t_tdata));
        end
    end

    // transfer interface path only has tlast high when tvalid is also high
    always_comb begin
        if (past_exists && t_tlast) begin
            T_LAST_VALID : assert(t_tvalid);
        end
    end

    // transfer interface path will only lower last after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(t_tlast)) begin
            T_LAST_LOWER : assert($past(t_tvalid && t_tready));
        end
    end

    // transfer interface path will only lower valid after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(t_tvalid)) begin
            T_VALID_LOWER : assert($past(t_tready));
        end
    end

    // transfer interface path will only lower ready after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(t_tready)) begin
            T_READY_LOWER : assert($past(t_tvalid));
        end
    end

`endif

endmodule

`ifndef YOSYS
`default_nettype wire
`endif
