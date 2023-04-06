/**
 * The AXI-Stream Arbiter allows for multiple 'up stream' slave ports to access
 * a single 'down stream' master. A slave port can request access to the master
 * by simply presenting to at the port, if more then one 'up stream' is
 * requesting ownership of the master port, the module will then use a
 * look-ahead, round-robin algorithm to select which slave port gets ownership
 * of the master port.
 *
 * The arbiter hands ownership of the master port to the slave port from right
 * to left (low to high address) pattern. Once the left most port has released
 * ownership the order wraps around and the right most port is given a chance
 * at ownership once again.
 *
 * Port ownership is released with the valid assertion of the 's_tlast' flag
 * that indicates the end of a stream. The module will stall when the
 * 'm_tready' flag deasserts.
 */

`default_nettype none

module axis_arbiter
  #(parameter   AXIS_DWIDTH = 2,
    parameter   PORT_NB     = 8)
   (input   wire    clk,
    input   wire    rst,

    input   wire    [PORT_NB*AXIS_DWIDTH-1:0]   s_tdata,
    input   wire    [PORT_NB-1:0]               s_tlast,
    input   wire    [PORT_NB-1:0]               s_tvalid,
    output  logic   [PORT_NB-1:0]               s_tready,

    output  logic   [AXIS_DWIDTH-1:0]   m_tdata,
    output  logic                       m_tlast,
    output  logic                       m_tvalid,
    input   wire                        m_tready
);

    localparam WRAP_LENGTH = 2*PORT_NB;

    integer a, b, c;

    logic done;
    logic next;
    logic idle;

    logic   [PORT_NB-1:0]       order;
    logic   [PORT_NB-1:0]       token;
    logic   [PORT_NB-1:0]       token_lookahead [PORT_NB];
    logic   [WRAP_LENGTH-1:0]   token_wrap;

    logic   [AXIS_DWIDTH-1:0]   skid_tdata [PORT_NB];
    logic   [PORT_NB-1:0]       skid_tlast;
    logic   [PORT_NB-1:0]       skid_tvalid;

    logic   [AXIS_DWIDTH-1:0]   s_tdata_i [PORT_NB];
    logic   [PORT_NB-1:0]       s_tlast_i;
    logic   [PORT_NB-1:0]       s_tvalid_i;
    logic                       m_active;

    always_comb begin
        done = |(s_tlast_i & s_tvalid_i) & m_active;
    end

    always_comb begin
        next = done | idle;
    end

    always_comb begin
        token_wrap = {token, token};
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            idle <= 1'b1;
        end
        else if (done) begin
            // ignoring the currently active slave port, we puts the arbiter
            // into an idle state if no other slave port is requesting
            // ownership of the master port.
            idle <= ~|(s_tvalid & ~token);
        end
        else if (idle) begin
            // when arbiter is in an idle state and there is a slave port
            // presenting with data, the idle state is deactivated.
            idle <= ~|(s_tvalid);
        end
    end

    // round-robin token ring
    always_ff @(posedge clk) begin
        if (rst) begin
            token <= 'b1;
        end
        else if (next) begin

            for (a = 0; a < PORT_NB; a = a + 1) begin : TOKEN_
                if (order[a]) begin
                    token <= token_lookahead[a];
                end
            end
        end
    end

    genvar y;
    generate
        for (y = 0; y < PORT_NB; y = y + 1) begin : ORDER_

            always_comb begin
                // calculate every possible 'next' token value with the highest
                // priority version being placed in the lowest address within
                // the unpacked lookahead variable
                token_lookahead[y] = token_wrap[y +: PORT_NB];
            end

            always_comb begin
                order[y] = |(token_lookahead[y] & s_tvalid);
            end

            // Skid register for master data value. The 'skid_tdata' variable
            // will store the data value that was (or would have been) written
            // on the master tdata output if the interface was 'ready'.
            always_ff @(posedge clk) begin
                skid_tdata[y] <= s_tdata_i[y];
            end

            // Skid register for master valid flag. The 'skid_tvalid' variable
            // will indicate when high that there is a pending 'valid' entry in
            // the skid buffers that have not been consumed by down stream.
            always_ff @(posedge clk) begin
                if (rst) begin
                    skid_tlast[y]   <= 1'b0;
                    skid_tvalid[y]  <= 1'b0;
                end
                else begin
                    skid_tlast[y]   <= s_tlast_i[y]     & ~(m_active & ~idle & token[y]);
                    skid_tvalid[y]  <= s_tvalid_i[y]    & ~(m_active & ~idle & token[y]);
                end
            end

            // skid mux: if 's_tready' is lowered the previous master values
            // that have not been passed to the downstream pipeline will be
            // held in the skid registers until they can be re-sent.
            always_comb begin
                s_tdata_i[y]    = s_tready[y] ? s_tdata[y*AXIS_DWIDTH +: AXIS_DWIDTH]   : skid_tdata[y];
                s_tlast_i[y]    = s_tready[y] ? s_tlast[y]                              : skid_tlast[y];
                s_tvalid_i[y]   = s_tready[y] ? s_tvalid[y]                             : skid_tvalid[y];
            end

            // when 'master' interface is ready or a 'slave' interface has
            // valid data, set slave interface ready to high if the modules
            // 'master' pipeline is not stalled
            always_ff @(posedge clk) begin
                if (rst) begin
                    s_tready[y] <= 1'b0;
                end
                else if (done) begin
                    s_tready[y] <= 1'b0;
                end
                else if (m_tready | s_tvalid[y]) begin
                    s_tready[y] <= m_active & ~idle & token[y];
                end
            end

        end
    endgenerate

    // 'master' interface mux will zero the output when no valid 'tdata'
    // prevent from changing when arbiter charges source
    always_ff @(posedge clk) begin
        if (m_active) begin

            m_tdata <= 'b0;
            for (b = 0; b < PORT_NB; b = b + 'd1) begin
                if (token[b] & s_tvalid_i[b]) begin
                    m_tdata <= s_tdata_i[b];
                end
            end
        end
    end

    // 'master' interface mux for 'tlast' and 'tvalid' control signals
    always_ff @(posedge clk) begin
        if (rst) begin
            m_tlast     <= 1'b0;
            m_tvalid    <= 1'b0;
        end
        else if (m_active) begin

            for (c = 0; c < PORT_NB; c = c + 'd1) begin
                if (token[c]) begin
                    m_tlast     <= s_tlast_i[c];
                    m_tvalid    <= s_tvalid_i[c];
                end
            end
        end
    end

    // Pipeline is active when empty or when master interface is ready.
    always_comb begin
        m_active = ~m_tvalid | m_tready;
    end


`ifdef FORMAL

`ifdef AXIS_ARBITER
    `define ASSUME assume
`else
    `define ASSUME assert
`endif

    function onehot0 (
        input logic [PORT_NB-1:0] testing
    );
        integer i;
        logic   valid;

        begin
            onehot0 = 1'b1;
            valid   = 1'b1;

            for (i = 0; i < PORT_NB; i = i + 1) begin
                if (testing[i]) begin
                    {onehot0, valid} = {valid, 1'b0};
                end
            end
        end
    endfunction

    function onehot (
        input logic [PORT_NB-1:0] testing
    );
        integer j;
        logic   valid;

        begin
            onehot  = 1'b0;
            valid   = 1'b1;

            for (j = 0; j < PORT_NB; j = j + 1) begin
                if (testing[j]) begin
                    {onehot, valid} = {valid, 1'b0};
                end
            end
        end
    endfunction

    logic   past_exists;
    logic   past_exists_1p;
    initial begin
        past_exists     = 1'b0;
        past_exists_1p  = 1'b0;

        // ensure reset is triggered at the start
        restrict property (rst == 1'b1);

        assume(idle ~& |(skid_tvalid));
        assume(idle ~& |(s_tready));

        assume(onehot(token));
        assume(onehot(token | skid_tvalid | skid_tlast));
        assume(onehot0(s_tready));
    end

    always_ff @(posedge clk) begin
        past_exists     <= 1'b1;
        past_exists_1p  <= past_exists;
    end

    always_comb begin
        assert(idle ~& |(skid_tvalid));
        assert(idle ~& |(s_tready));

        assert(onehot(token));
        assert(onehot(token | skid_tvalid | skid_tlast));
        assert(onehot0(s_tready));
    end

    // Token should never stay for only one cycle as this does not give enough
    // time for that port to be serviced
    always_ff @(posedge clk) begin
        if (past_exists_1p && ~rst && $past(~rst)  && $past(~rst, 2) && $changed(token)) begin
            TOKEN_NO_SKIP : assert($past(token) == $past(token, 2));
        end
    end

    // the arbiter will become idle when a stream ends and no other actor/port
    // is requesting ownership of downstream
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(done) && idle) begin
            IDLE_ENTERED : assert(onehot($past(s_tvalid | token)));
        end
    end

    genvar x;
    generate
        for (x = 0; x < PORT_NB; x = x + 1) begin : SLAVE_FORMAL_

            //
            // Check the proper relationship between slave interface bus signals
            //

            // slave interface path holds data steady when stalled
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $past(s_tvalid[x] && ~s_tready[x])) begin
                    `ASSUME($stable(s_tdata[x*AXIS_DWIDTH +: AXIS_DWIDTH]));
                end
            end

            // slave interface path only has tlast high when tvalid is also high
            always_comb begin
                if (past_exists && s_tlast[x]) begin
                    `ASSUME(s_tvalid[x]);
                end
            end

            // slave interface path will only lower last after a transaction
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $fell(s_tlast[x])) begin
                    `ASSUME($past(s_tvalid[x] && s_tready[x]));
                end
            end

            // slave interface path will only lower valid after a transaction
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $fell(s_tvalid[x])) begin
                    `ASSUME($past(s_tready[x]));
                end
            end

            // slave interface path will only lower ready after a transaction
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $fell(s_tready[x])) begin
                    assert($past(s_tvalid[x]));
                end
            end

            // arbiter will not raise s_tready unless arbiter is active (not idle)
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $rose(s_tready[x])) begin
                    assert($stable(~idle));
                end
            end

            // slave interface ready will only be high if the token has selected that port
            always_comb begin
                if (past_exists && s_tready[x]) begin
                    assert(token[x]);
                end
            end

            //
            // Check the proper relationship with skid logic
            //

            // skid logic holds data steady when back pressure is being applied
            always_ff @(posedge clk) begin
                if (past_exists && $past(~s_tready[x])) begin
                    assert($stable(skid_tdata[x]));
                end
            end

            // skid logic holds last slave data value when back pressure is
            // applied
            always_ff @(posedge clk) begin
                if (past_exists && $fell(s_tready[x])) begin
                    assert(skid_tdata[x] == $past(s_tdata[x*AXIS_DWIDTH +: AXIS_DWIDTH]));
                end
            end

            // master data sourced from slave data
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $past(m_tready && s_tready[x] && s_tvalid[x])) begin
                    assert(m_tdata == $past(s_tdata[x*AXIS_DWIDTH +: AXIS_DWIDTH]));
                end
            end

            // master data sourced from skid data
            always_ff @(posedge clk) begin
                if (past_exists && ~rst && $past(~rst) && $past(m_tready && ~s_tready[x] && skid_tvalid[x])) begin
                    assert(m_tdata == $past(skid_tdata[x]));
                end
            end

            // skid tlast should be high only when skid tvalid is high
            always_comb begin
                if (past_exists && skid_tlast[x]) begin
                    assert(skid_tvalid[x]);
                end
            end
        end
    endgenerate

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

`ifndef YOSYS
`default_nettype wire
`endif
