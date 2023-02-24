/**
 * The AXI-Stream skid buffer module registers the ready signal and compensates
 * for the delay using by using a diversion 'skid' register.
 */

`default_nettype none

module axis_skid_buffer
  #(parameter   GREEDY      = 0,
    parameter   AXIS_DWIDTH = 32)
   (input   wire    clk,
    input   wire    rst,

    input   wire    [AXIS_DWIDTH-1:0]   s_tdata,
    input   wire                        s_tlast,
    input   wire                        s_tvalid,
    output  logic                       s_tready,

    output  logic   [AXIS_DWIDTH-1:0]   m_tdata,
    output  logic                       m_tlast,
    output  logic                       m_tvalid,
    input   wire                        m_tready
);

    logic   [AXIS_DWIDTH-1:0]   skid_tdata;
    logic                       skid_tlast;
    logic                       skid_tvalid;

    logic   [AXIS_DWIDTH-1:0]   s_tdata_i;
    logic                       s_tlast_i;
    logic                       s_tvalid_i;
    logic                       m_active;

    // Skid register for master data value. The 'skid_tdata' variable will
    // store the data value that was (or would have been) written on the master
    // tdata output if the interface was 'ready'.
    always_ff @(posedge clk) begin
        skid_tdata <= s_tdata_i;
    end

    // Skid register for master valid flag. The 'skid_tvalid' variable will
    // indicate when high that there is a pending 'valid' entry in the
    // skid buffers that have not been consumed by down stream.
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

    // when 'master' stream is ready or 'slave' stream has valid data, set
    // 'slave' ready to high if the modules 'master' pipeline is not stalled
    generate
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
    endgenerate

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

    // Pipiline is active when empty or when master interface is ready.
    always_comb begin
        m_active = ~m_tvalid | m_tready;
    end


`ifdef FORMAL

`ifdef AXIS_SKID_BUFFER
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
endmodule

`ifdef YOSYS
`default_nettype wire
`endif
