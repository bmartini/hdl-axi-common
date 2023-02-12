/**
 * Converts an axi4lite interface into a register/BRAM read/write interface.
 */

`default_nettype none

module axi4lite_reg
  #(parameter   AXI_DWIDTH  = 32,
    parameter   AXI_AWIDTH  = 7,
    localparam  CFG_DWIDTH  = AXI_DWIDTH,
    localparam  CFG_AWIDTH  = (AXI_AWIDTH - $clog2(CFG_DWIDTH / 8)))
   (input   wire    clk,
    input   wire    rst,

    input   wire    [AXI_AWIDTH-1:0]    axil_awaddr,
    input   wire    [2:0]               axil_awprot,
    input   wire                        axil_awvalid,
    output  logic                       axil_awready,

    input   wire    [AXI_DWIDTH-1:0]    axil_wdata,
    input   wire    [AXI_DWIDTH/8-1:0]  axil_wstrb,
    input   wire                        axil_wvalid,
    output  logic                       axil_wready,

    output  logic   [1:0]               axil_bresp,
    output  logic                       axil_bvalid,
    input   wire                        axil_bready,

    input   wire    [AXI_AWIDTH-1:0]    axil_araddr,
    input   wire    [2:0]               axil_arprot,
    input   wire                        axil_arvalid,
    output  logic                       axil_arready,

    output  logic   [AXI_DWIDTH-1:0]    axil_rdata,
    output  logic   [1:0]               axil_rresp,
    output  logic                       axil_rvalid,
    input   wire                        axil_rready,

    output  logic   [CFG_DWIDTH-1:0]    cfg_wr_data,
    output  logic   [CFG_AWIDTH-1:0]    cfg_wr_addr,
    output  logic                       cfg_wr_en,

    input   wire    [CFG_DWIDTH-1:0]    cfg_rd_data,
    output  logic   [CFG_AWIDTH-1:0]    cfg_rd_addr,
    output  logic                       cfg_rd_en
);

    localparam OFFSET = AXI_AWIDTH - CFG_AWIDTH;

    logic   axil_resp_active;
    logic   skid_wr_resp_en;
    logic   cfg_wr_resp_ready;
    logic   cfg_wr_resp_en_i;
    logic   cfg_wr_resp_en;

    logic [CFG_AWIDTH-1:0]  skid_awaddr;
    logic                   skid_awvalid;

    logic [CFG_AWIDTH-1:0]  cfg_wr_addr_i;
    logic                   cfg_wr_addr_en;
    logic                   cfg_wr_addr_en_i;
    logic                   cfg_wr_addr_active;
    logic                   cfg_wr_addr_ready;

    logic [CFG_DWIDTH-1:0]  skid_wdata;
    logic                   skid_wvalid;

    logic [CFG_DWIDTH-1:0]  cfg_wr_data_i;
    logic                   cfg_wr_data_en;
    logic                   cfg_wr_data_en_i;
    logic                   cfg_wr_data_active;
    logic                   cfg_wr_data_ready;

    logic [CFG_AWIDTH-1:0]  skid_araddr;
    logic                   skid_arvalid;

    logic [CFG_AWIDTH-1:0]  cfg_rd_addr_i;
    logic                   cfg_rd_addr_en;
    logic                   cfg_rd_addr_en_i;
    logic                   cfg_rd_addr_ready;

    logic [CFG_DWIDTH-1:0]  skid_rd_data;
    logic                   skid_rd_valid;

    logic [CFG_DWIDTH-1:0]  axil_rdata_i;
    logic                   axil_rvalid_i;
    logic                   axil_rd_data_active;
    logic                   cfg_rd_data_en;
    logic                   cfg_rd_data_ready;


    /**
     * Implementation of Write Path
     */

    // Only when all 3 write channels (addr, data and response) are primed and
    // ready will a cfg add/data pair be released.
    always_comb begin
        cfg_wr_en           = cfg_wr_addr_en & cfg_wr_data_en & cfg_wr_resp_ready;
        cfg_wr_resp_en      = cfg_wr_addr_en & cfg_wr_data_en;
        cfg_wr_data_ready   = cfg_wr_addr_en & cfg_wr_resp_ready;
        cfg_wr_addr_ready   = cfg_wr_data_en & cfg_wr_resp_ready;
    end


    /**
     * Implementation of Write Response Path
     */

    // Skid register for write response enable flag. The 'skid_wr_resp_en'
    // variable will indicate when high that there is a valid response in the
    // skid write register that has not been consumed by the axi4lite
    // interface.
    always_ff @(posedge clk) begin
        if (rst)    skid_wr_resp_en <= 1'b0;
        else        skid_wr_resp_en <= cfg_wr_resp_en_i & ~axil_resp_active;
    end

    // Write response mux: if 'cfg_wr_resp_ready' is lowered the previous value that
    // have not been passed to the next pipeline stage and must be re-sent
    // using the values stored in the skid registers.
    always_comb begin
        cfg_wr_resp_en_i = cfg_wr_resp_ready ? cfg_wr_resp_en : skid_wr_resp_en;
    end

    // When axi4lite write response interface is ready or write data was sent
    // on the cfg_wr_data interface, set write response reciver interface to
    // ready.
    always_ff @(posedge clk) begin
        if      (rst)                               cfg_wr_resp_ready <= 1'b0;
        else if (axil_resp_active | cfg_wr_resp_en) cfg_wr_resp_ready <= axil_resp_active;
    end

    always_ff @(posedge clk) begin
        if      (rst)               axil_bvalid <= 1'b0;
        else if (axil_resp_active)  axil_bvalid <= cfg_wr_resp_en_i;
    end

    // do not stall Write Response pipeline until it is primed
    always_comb begin
        axil_resp_active = ~axil_bvalid | axil_bready;
    end

    // write response is forever 'OKAY'
    always_comb begin
        axil_bresp = 2'b0;
    end


    /**
     * Implementation of Write Address Path
     */

    // Skid register for write address value. The 'skid_awaddr' variable will
    // store an address that was (or would have been) written on the cfg wr
    // address output if the cfg interface was 'ready'.
    always_ff @(posedge clk) begin
        skid_awaddr <= cfg_wr_addr_i;
    end

    // Skid register for write address valid flag. The 'skid_awvalid' variable
    // will indicate when high that there is a pending 'valid' entry in the
    // skid address register that has not been consumed by the cfg interface.
    always_ff @(posedge clk) begin
        if (rst)    skid_awvalid <= 1'b0;
        else        skid_awvalid <= cfg_wr_addr_en_i & ~cfg_wr_addr_active;
    end

    // Write address mux: if 'axil_awready' is lowered the previous cfg values
    // that have not been passed to the downstream cfg pipeline will be held in
    // the skid registers until they can be re-sent.
    always_comb begin
        cfg_wr_addr_i       = axil_awready  ? axil_awaddr[OFFSET +: CFG_AWIDTH] : skid_awaddr;
        cfg_wr_addr_en_i    = axil_awready  ? axil_awvalid                      : skid_awvalid;
    end

    // When the cfg write 'addr' interface is active or the axi4lite write
    // address interface has a valid address, we set the axi4lite ready to
    // the same value as the 'active' value.
    always_ff @(posedge clk) begin
        if      (rst)                               axil_awready <= 1'b0;
        else if (cfg_wr_addr_active | axil_awvalid) axil_awready <= cfg_wr_addr_active;
    end

    always_ff @(posedge clk) begin
        if (cfg_wr_addr_active) begin
            cfg_wr_addr <= 'b0;

            if (cfg_wr_addr_en_i) begin
                cfg_wr_addr <= cfg_wr_addr_i;
            end
        end
    end

    always_ff @(posedge clk) begin
        if      (rst)                   cfg_wr_addr_en <= 1'b0;
        else if (cfg_wr_addr_active)    cfg_wr_addr_en <= cfg_wr_addr_en_i;
    end

    // Write address pipiline is active when empty or when cfg write address
    // path is ready.
    always_comb begin
        cfg_wr_addr_active = ~cfg_wr_addr_en | cfg_wr_addr_ready;
    end


    /**
     * Implementation of Write Data Path
     */

    // Skid register for write data value. The 'skid_wdata' variable will store
    // the data that was (or would have been) written on the cfg wr data output
    // if the cfg interface was 'ready'.
    always_ff @(posedge clk) begin
        skid_wdata <= cfg_wr_data_i;
    end

    // Skid register for write data valid flag. The 'skid_wvalid' variable will
    // indicate when high that there is a pending 'valid' entry in the skid
    // data register that has not been consumed by the cfg interface.
    always_ff @(posedge clk) begin
        if (rst)    skid_wvalid <= 1'b0;
        else        skid_wvalid <= cfg_wr_data_en_i & ~cfg_wr_data_active;
    end

    // Write data mux: if 'axil_wready' is lowered the previous cfg values that
    // have not been passed to the downstream cfg pipeline will be held in the
    // skid registers until they can be re-sent.
    always_comb begin
        cfg_wr_data_i       = axil_wready   ? axil_wdata    : skid_wdata;
        cfg_wr_data_en_i    = axil_wready   ? axil_wvalid   : skid_wvalid;
    end

    // When the cfg write data interface is active or the axi4lite write data
    // interface has valid data, we set the axi4lite data ready to the 'active'
    // value.
    always_ff @(posedge clk) begin
        if      (rst)                               axil_wready <= 1'b0;
        else if (cfg_wr_data_active | axil_wvalid)  axil_wready <= cfg_wr_data_active;
    end

    always_ff @(posedge clk) begin
        if (cfg_wr_data_active) begin
            cfg_wr_data <= 'b0;

            if (cfg_wr_data_en_i) begin
                cfg_wr_data <= cfg_wr_data_i;
            end
        end
    end

    always_ff @(posedge clk) begin
        if      (rst)                   cfg_wr_data_en <= 1'b0;
        else if (cfg_wr_data_active)    cfg_wr_data_en <= cfg_wr_data_en_i;
    end

    // Write data pipiline is active when empty or when cfg write data path is
    // ready.
    always_comb begin
        cfg_wr_data_active = ~cfg_wr_data_en | cfg_wr_data_ready;
    end


    /**
     * Implementation of Read Address Path
     */

    // Skid register for read address value. The 'skid_araddr' variable will
    // store an address that was (or would have been) written on the cfg rd
    // address output if the cfg interface was 'ready'.
    always_ff @(posedge clk) begin
        skid_araddr <= cfg_rd_addr_i;
    end

    // Skid register for read address valid flag. The 'skid_arvalid' variable
    // will indicate when high that there is a pending 'valid' entry in the
    // skid read address register that has not been consumed by the cfg
    // interface.
    always_ff @(posedge clk) begin
        if (rst)    skid_arvalid <= 1'b0;
        else        skid_arvalid <= cfg_rd_addr_en_i & ~cfg_rd_addr_ready;
    end

    // Read address mux: if 'axil_arready' is lowered the previous cfg values
    // that have not been passed to the downstream cfg pipeline will be held in
    // the skid registers until they can be re-sent.
    always_comb begin
        cfg_rd_addr_i       = axil_arready  ? axil_araddr[OFFSET +: CFG_AWIDTH] : skid_araddr;
        cfg_rd_addr_en_i    = axil_arready  ? axil_arvalid                      : skid_arvalid;
    end

    // When the cfg read 'addr' interface is ready or the axi4lite read address
    // interface has a valid address, we set the axi4lite ready to the same
    // value as the cfg address ready value.
    always_ff @(posedge clk) begin
        if      (rst)                               axil_arready <= 1'b0;
        else if (cfg_rd_addr_ready | axil_arvalid)  axil_arready <= cfg_rd_addr_ready;
    end

    always_ff @(posedge clk) begin
        if (cfg_rd_addr_ready) begin
            cfg_rd_addr <= 'b0;

            if (cfg_rd_addr_en_i) begin
                cfg_rd_addr <= cfg_rd_addr_i;
            end
        end
    end

    always_ff @(posedge clk) begin
        if      (rst)               cfg_rd_addr_en <= 1'b0;
        else if (cfg_rd_addr_ready) cfg_rd_addr_en <= cfg_rd_addr_en_i;
    end

    // Read address pipiline is ready when empty or when axi4lite read address
    // path is ready.
    always_comb begin
        cfg_rd_addr_ready = ~cfg_rd_addr_en | axil_rready;
    end

    always_ff @(posedge clk) begin
        if (rst)    cfg_rd_en <= 1'b0;
        else        cfg_rd_en <= cfg_rd_addr_ready & cfg_rd_addr_en_i;
    end


    /**
     * Implementation of Read Data Path
     */

    // Read transaction response is forever 'OKAY'
    always_comb begin
        axil_rresp = 2'b0;
    end

    // Skid register for read data value. The 'skid_rd_data' variable will
    // store the data that was (or would have been) written on the axi4lite
    // read data channel if the axi4lite channel was 'ready'.
    always_ff @(posedge clk) begin
        skid_rd_data <= axil_rdata_i;
    end

    // Skid register for read data valid flag. The 'skid_rd_valid' variable
    // will indicate when high that there is a pending 'valid' entry in the
    // skid read data register that has not been consumed by the cfg interface.
    always_ff @(posedge clk) begin
        if (rst)    skid_rd_valid <= 1'b0;
        else        skid_rd_valid <= axil_rvalid_i & ~axil_rready;
    end

    // Read data mux: if 'cfg_rd_data_ready' is lowered the previous axi4lite
    // read data values that have not been passed to the axi4lite read data
    // channel will be held in the skid registers until they can be re-sent.
    always_comb begin
        axil_rdata_i    = cfg_rd_data_ready ? cfg_rd_data       : skid_rd_data;
        axil_rvalid_i   = cfg_rd_data_ready ? cfg_rd_data_en    : skid_rd_valid;
    end

    // The cfg read data valid signal is generated internally, one cycle after
    // the read address was sent.
    always_ff @(posedge clk) begin
        if      (rst)               cfg_rd_data_en <= 1'b0;
        else if (cfg_rd_en)         cfg_rd_data_en <= 1'b1;
        else if (cfg_rd_data_ready) cfg_rd_data_en <= 1'b0;
    end

    // When the axi4lite read data pipeline is 'active' the cfg read data
    // channel ready flag is set to the same value as the axi4lite read data
    // 'active' value.
    always_ff @(posedge clk) begin
        if      (rst)                   cfg_rd_data_ready <= 1'b0;
        else if (axil_rd_data_active)   cfg_rd_data_ready <= axil_rd_data_active;
    end

    always_ff @(posedge clk) begin
        if (axil_rd_data_active) begin
            axil_rdata <= axil_rdata_i;
        end
    end

    always_ff @(posedge clk) begin
        if      (rst)                   axil_rvalid <= 1'b0;
        else if (axil_rd_data_active)   axil_rvalid <= axil_rvalid_i;
    end

    always_comb begin
        axil_rd_data_active = ~axil_rvalid | axil_rready;
    end


`ifdef FORMAL

`ifdef AXI4LITE_REG
    `define ASSUME assume
`else
    `define ASSUME assert
`endif

    reg past_exists;
    initial begin
        past_exists = 1'b0;

        // ensure reset is triggered at the start
        restrict property (rst == 1'b1);
    end

    always_ff @(posedge clk) begin
        past_exists <= 1'b1;
    end

    //
    // Check the proper relationship between axi4lite write response interface signals
    //

    // write response channel holds value steady when stalled
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(axil_bvalid && ~axil_bready)) begin
            B_RESP_STABLE : assert($stable(axil_bresp));
        end
    end

    // write response channel will only lower valid after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(axil_bvalid)) begin
            B_VALID_LOWER : assert($past(axil_bready));
        end
    end

    // write response channel will only lower ready after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(axil_bready)) begin
            B_READY_LOWER : `ASSUME($past(axil_bvalid));
        end
    end

    //
    // Check the proper relationship between axi4lite write address interface signals
    //

    // write address channel holds value steady when stalled
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(axil_awvalid && ~axil_awready)) begin
            AW_ADDR_STABLE : `ASSUME($stable(axil_awaddr));
            AW_PROT_STABLE : `ASSUME($stable(axil_awprot));
        end
    end

    // write address channel will only lower valid after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(axil_awvalid)) begin
            AW_VALID_LOWER : `ASSUME($past(axil_awready));
        end
    end

    // write address channel will only lower ready after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(axil_awready)) begin
            AW_READY_LOWER : assert($past(axil_awvalid));
        end
    end

    //
    // Check the proper relationship between axi4lite write data interface signals
    //

    // write data channel holds value steady when stalled
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(axil_wvalid && ~axil_wready)) begin
            W_DATA_STABLE : `ASSUME($stable(axil_wdata));
            W_STRB_STABLE : `ASSUME($stable(axil_wstrb));
        end
    end

    // write data channel will only lower valid after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(axil_wvalid)) begin
            W_VALID_LOWER : `ASSUME($past(axil_wready));
        end
    end

    // write data channel will only lower ready after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(axil_wready)) begin
            W_READY_LOWER : assert($past(axil_wvalid));
        end
    end

    //
    // Check the proper relationship between axi4lite read address interface signals
    //

    // read address channel holds value steady when stalled
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(axil_arvalid && ~axil_arready)) begin
            AR_ADDR_STABLE : `ASSUME($stable(axil_araddr));
            AR_PROT_STABLE : `ASSUME($stable(axil_arprot));
        end
    end

    // read address channel will only lower valid after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(axil_awvalid)) begin
            AR_VALID_LOWER : `ASSUME($past(axil_awready));
        end
    end

    // read address channel will only lower ready after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(axil_awready)) begin
            AR_READY_LOWER : assert($past(axil_awvalid));
        end
    end

    //
    // Check the proper relationship between axi4lite read data interface signals
    //

    // read data channel holds value steady when stalled
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(axil_rvalid && ~axil_rready)) begin
            R_DATA_STABLE : assert($stable(axil_rdata));
            R_RESP_STABLE : assert($stable(axil_rresp));
        end
    end

    // read data channel will only lower valid after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(axil_rvalid)) begin
            R_VALID_LOWER : assert($past(axil_rready));
        end
    end

    // read data channel will only lower ready after a transaction
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $fell(axil_rready)) begin
            R_READY_LOWER : `ASSUME($past(axil_rvalid));
        end
    end

    //
    // Check the proper relationship between cfg write interface signals
    //

    // pass through mode has the cfg write address output sourced from the axi4lite inputs
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(cfg_wr_addr_en_i && cfg_wr_addr_active && axil_awready)) begin
            CFG_FROM_AXIL_AWADDR : assert(cfg_wr_addr == $past(axil_awaddr[OFFSET +: CFG_AWIDTH]));
        end
    end

    // backpressure mode has the cfg write address output sourced from the skid registers
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(cfg_wr_addr_en_i && cfg_wr_addr_active && ~axil_awready)) begin
            CFG_FROM_SKID_AWADDR : assert(cfg_wr_addr == $past(skid_awaddr));
        end
    end

    // pass through mode has the cfg write data output sourced from the axi4lite inputs
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(cfg_wr_data_en_i && cfg_wr_data_active && axil_wready)) begin
            CFG_FROM_AXIL_WDATA : assert(cfg_wr_data == $past(axil_wdata));
        end
    end

    // backpressure mode has the cfg write data output sourced from the skid registers
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(cfg_wr_data_en_i && cfg_wr_data_active && ~axil_wready)) begin
            CFG_FROM_SKID_WDATA : assert(cfg_wr_data == $past(skid_wdata));
        end
    end

    //
    // Check the proper relationship between cfg read interface signals
    //

    // pass through mode has the cfg read address output sourced from the axi4lite inputs
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(cfg_rd_addr_en_i && cfg_rd_addr_ready && axil_arready)) begin
            CFG_FROM_AXIL_ARADDR : assert(cfg_rd_addr == $past(axil_araddr[OFFSET +: CFG_AWIDTH]));
        end
    end

    // backpressure mode has the cfg read address output sourced from the skid registers
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(cfg_rd_addr_en_i && cfg_rd_addr_ready && ~axil_arready)) begin
            CFG_FROM_SKID_ARADDR : assert(cfg_rd_addr == $past(skid_araddr));
        end
    end

    // pass through mode has the axil read data output sourced from the cfg read data input
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(axil_rvalid && axil_rready && cfg_rd_data_ready)) begin
            CFG_FROM_AXIL_RDATA : assert(axil_rdata == $past(cfg_rd_data));
        end
    end

    // backpressure mode has the axil read data output sourced from the skid registers
    always_ff @(posedge clk) begin
        if (past_exists && ~rst && $past(~rst) && $past(axil_rvalid && axil_rready && ~cfg_rd_data_ready)) begin
            CFG_FROM_SKID_RDATA : assert(axil_rdata == $past(skid_rd_data));
        end
    end

`endif
endmodule

`ifdef YOSYS
`default_nettype wire
`endif
