/**
 * A simple FIFO, with synchronous clock for both the pop and push ports.
 */

`default_nettype none

module axis_fifo
  #(parameter DATA_WIDTH  = 16,
    parameter ADDR_WIDTH  = 16)
   (input   wire    clk,
    input   wire    rst,

    input   wire    [DATA_WIDTH-1:0]    s_tdata,
    input   wire                        s_tlast,
    input   wire                        s_tvalid,
    output  logic                       s_tready,

    output  logic   [DATA_WIDTH-1:0]    m_tdata,
    output  logic                       m_tlast,
    output  logic                       m_tvalid,
    input   wire                        m_tready
);

    localparam FIFO_WIDTH   = DATA_WIDTH + 1;
    localparam DEPTH        = 1 << ADDR_WIDTH;

    logic   [FIFO_WIDTH-1:0]    mem [DEPTH];

    logic                       full;
    logic                       full_nx;
    logic                       empty;
    logic                       empty_nx;

    logic                       push;
    logic   [FIFO_WIDTH-1:0]    push_data;
    logic   [ADDR_WIDTH-1:0]    push_addr;
    logic   [ADDR_WIDTH-1:0]    push_addr_nx;
    logic   [ADDR_WIDTH:0]      push_ptr;
    logic   [ADDR_WIDTH:0]      push_ptr_nx;

    logic                       pop;
    logic   [FIFO_WIDTH-1:0]    pop_data;
    logic   [ADDR_WIDTH-1:0]    pop_addr;
    logic   [ADDR_WIDTH-1:0]    pop_addr_nx;
    logic   [ADDR_WIDTH:0]      pop_ptr;
    logic   [ADDR_WIDTH:0]      pop_ptr_nx;
    logic                       pop_valid;

    logic   [FIFO_WIDTH-1:0]    skid_tdata;
    logic                       skid_tvalid;

    logic   [FIFO_WIDTH-1:0]    m_tdata_ii;
    logic   [FIFO_WIDTH-1:0]    m_tdata_i;
    logic                       m_tvalid_i;
    logic                       m_active;

    /*
     * Convert Slave AXIS to FIFO interface
     */

    always_comb begin
        push        = s_tvalid;
        push_data   = {s_tdata, s_tlast};
        s_tready    = ~full;
    end

    /*
     * Implementation of Generic FIFO
     */

    always_comb begin
        push_addr    = push_ptr      [ADDR_WIDTH-1:0];
        push_addr_nx = push_ptr_nx   [ADDR_WIDTH-1:0];
        pop_addr     = pop_ptr       [ADDR_WIDTH-1:0];
        pop_addr_nx  = pop_ptr_nx    [ADDR_WIDTH-1:0];
    end

    always_comb begin
        // full next
        full_nx = (push_addr_nx == pop_addr_nx)
                    & (push_ptr_nx[ADDR_WIDTH] != pop_ptr_nx[ADDR_WIDTH]);

        // empty next
        empty_nx = (push_addr_nx == pop_addr_nx)
                    & (push_ptr_nx[ADDR_WIDTH] == pop_ptr_nx[ADDR_WIDTH]);
    end

    always_comb begin
        // pop pointer next
        pop_ptr_nx = pop_ptr + {{ADDR_WIDTH-1{1'b0}}, (pop & ~empty)};

        // push pointer next
        push_ptr_nx = push_ptr + {{ADDR_WIDTH-1{1'b0}}, (push & ~full)};
    end

    // registered full flag
    always_ff @(posedge clk) begin
        if (rst)    full    <= 1'b0;
        else        full    <= full_nx;
    end

    // registered empty flag
    always_ff @(posedge clk) begin
        if (rst)    empty   <= 1'b1;
        else        empty   <= empty_nx;
    end

    // memory read-address pointer
    always_ff @(posedge clk) begin
        if (rst)    pop_ptr <= '0;
        else        pop_ptr <= pop_ptr_nx;
    end

    // read from memory
    always_ff @(posedge clk) begin
        if (pop & ~empty) begin
            pop_data <= mem[pop_addr];
        end
    end

    // memory write-address pointer
    always_ff @(posedge clk) begin
        if (rst)    push_ptr    <= '0;
        else        push_ptr    <= push_ptr_nx;
    end

    // write to memory
    always_ff @(posedge clk) begin
        if (push & ~full) begin
            mem[push_addr] <= push_data;
        end
    end

    /*
     * Convert FIFO to Master AXIS interface
     */

    // stallable fifo valid flag
    always_ff @(posedge clk) begin
        if      (rst)   pop_valid <= 1'b0;
        else if (pop)   pop_valid <= ~empty;
    end

    // skid_tdata always reflects downstream data's last cycle
    always_ff @(posedge clk) begin
        skid_tdata <= m_tdata_i;
    end

    // skid_tvalid remembers if there is valid data in the skid register until
    // it's consumed by the downstream
    always_ff @(posedge clk) begin
        if (rst)    skid_tvalid <= 1'b0;
        else        skid_tvalid <= m_tvalid_i & ~m_active;
    end

    // down stream mux: when pop is not active, use last cycle's data and valid
    always_comb begin
        m_tdata_i   = pop ? pop_data    : skid_tdata;
        m_tvalid_i  = pop ? pop_valid   : skid_tvalid;
    end

    // when down stream is active, pop upstream fifo
    always_ff @(posedge clk) begin
        if (rst)    pop <= 1'b0;
        else        pop <= m_active;
    end

    always_ff @(posedge clk) begin
        if      (rst)       m_tvalid <= 1'b0;
        else if (m_active)  m_tvalid <= m_tvalid_i;
    end

    always_ff @(posedge clk) begin
        if (m_active) begin
            m_tdata_ii <= m_tdata_i;
        end
    end

    // do not stall pipeline until it is primed
    always_comb begin
        m_active = ~m_tvalid | m_tready;
    end

    always_comb begin
        m_tdata = m_tdata_ii[1 +: DATA_WIDTH];
        m_tlast = m_tdata_ii[0] & m_tvalid;
    end

`ifdef FORMAL

`ifdef AXIS_FIFO
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
    // Check that counters and pointers stay within their relative ranges
    //

    // impossible state of being both full and empty
    always_comb begin
        if (~rst) begin
            IMPOSSIBLE : assert(~(empty && full));
        end
    end

    // tests direction of pointer travel, push incrementing to 'full'
    always_comb begin
        if (~rst && (push_ptr >= pop_ptr)) begin
            DEPTH_INCREACING : assert((push_ptr - pop_ptr) <= DEPTH);
        end
    end

    // tests direction of pointer travel, pop incrementing to 'empty'
    always_comb begin
        if (~rst && (push_ptr < pop_ptr)) begin
            DEPTH_DECREACING : assert((pop_ptr - push_ptr) >= DEPTH);
        end
    end

    //
    // Check that pop behavior is consistent
    //

    // popping from an empty FIFO will not change the pop addr or data register
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(pop && empty)) begin
            EMPTY_POP_ADDR : assert($stable(pop_addr));
            EMPTY_POP_DATA : assert($stable(pop_data));
        end
    end

    // empty signal asserted only after data is popped
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $rose(empty)) begin
            EMPTY_ROSE : assert($past(pop));
        end
    end

    // empty signal asserted when both pointers are equal
    always_comb begin
        if (~rst) begin
            EMPTY_TRUE : assert(empty == (pop_ptr == push_ptr));
        end
    end

    //
    // Check that push behavior is consistent
    //

    // pushing into a full FIFO will not change the push addr or mem data
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(push && full)) begin
            FULL_PUSH_ADDR : assert($stable(push_addr));
            FULL_PUSH_DATA : assert($stable(mem[push_addr]));
        end
    end

    // full signal asserted only after data is pushed
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $rose(full)) begin
            FULL_ROSE : assert($past(push));
        end
    end

    // full signal asserted when both pointers are not equal but addrs are
    always_comb begin
        if (~rst) begin
            FULL_TRUE : assert(full == ((pop_ptr != push_ptr) && (pop_addr == push_addr)));
        end
    end

    //
    // Check that some fundamental use cases are valid
    //

    logic   f_full_state_reached = 1'b0;
    always_ff @(posedge clk) begin
        if      (rst)   f_full_state_reached <= 1'b0;
        else if (full)  f_full_state_reached <= 1'b1;
    end

    // show that the FIFO can fill up and then return to empty, traveling the
    // entire range of the FIFO depth and thus able to test all assert
    // statements
    always_comb begin
        cover(f_full_state_reached && empty);
    end

    //
    // Check the proper relationship with skid logic
    //

    // skid logic holds data steady when back pressure is being applied
    always_ff @(posedge clk) begin
        if (past_exists && $past(~pop)) begin
            SKID_DATA_STABLE : assert($stable(skid_tdata));
        end
    end

    // skid logic holds last slave data value when back pressure is applied
    always_ff @(posedge clk) begin
        if (past_exists && $fell(pop)) begin
            SKID_DATA_UPDATE : assert(skid_tdata == $past(pop_data));
        end
    end

    // skid logic holds control signals steady when back pressure is being applied
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $stable(~pop)) begin
            SKID_VALID_STABLE : assert($stable(skid_tvalid));
        end
    end

    //
    // Check that the master data is sourced from correct locations
    //

    // master data sourced from pop data
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(m_tready && pop)) begin
            M_FROM_S_UPDATE : assert(m_tdata_ii == $past(pop_data));
        end
    end

    // master data sourced from skid data
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(m_tready && ~pop)) begin
            M_FROM_SKID_UPDATE : assert(m_tdata_ii == $past(skid_tdata));
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

`ifndef YOSYS
`default_nettype wire
`endif
