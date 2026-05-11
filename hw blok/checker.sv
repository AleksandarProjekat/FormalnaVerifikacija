`timescale 1ns/1ps

module sort_ip #(
    parameter int N = 1024
)(
    input  logic        clk,
    input  logic        rst,

    input  logic        ain_tvalid,
    output logic        ain_tready,
    input  logic [31:0] ain_tdata,
    input  logic        ain_tlast,

    output logic        aout_tvalid,
    input  logic        aout_tready,
    output logic [31:0] aout_tdata,
    output logic        aout_tlast,

    input  logic        sort_dir,
    output logic [31:0] dup_nums
);

    localparam int ELEM_W = 16;
    localparam int BEATS  = N / 2;
    localparam int IDXW   = $clog2(N);
    localparam int BTW    = (BEATS <= 1) ? 1 : $clog2(BEATS);

    typedef enum logic [1:0] { S_IDLE, S_LOAD, S_SORT, S_OUT } state_t;
    state_t st;

    logic [ELEM_W-1:0] mem      [0:N-1];
    logic [ELEM_W-1:0] mem_next [0:N-1];

    logic [BTW-1:0]         in_b;
    logic [BTW-1:0]         out_b;
    logic [$clog2(N+1)-1:0] pass;

    logic sort_dir_lat;

    logic [IDXW-1:0] in_idx0, in_idx1;
    logic [IDXW-1:0] out_idx0, out_idx1;

    logic [ELEM_W-1:0] o0, o1;

    logic [31:0]       dup_cnt;
    logic [1:0]        dup_add; 
    logic [ELEM_W-1:0] prev_val;
    logic              prev_valid;


    always_comb begin
        ain_tready  = (st == S_LOAD);
        aout_tvalid = (st == S_OUT);
        
        in_idx0  = {in_b, 1'b0};
        in_idx1  = in_idx0 + 1'b1;
        out_idx0 = {out_b, 1'b0};
        out_idx1 = out_idx0 + 1'b1;
        
        o0         = mem[out_idx0];
        o1         = mem[out_idx1];
        aout_tdata = {o1, o0};
    end

    assign aout_tlast = (st == S_OUT) && (out_b == (BEATS[BTW-1:0] - 1'b1));
    assign dup_nums   = dup_cnt;


    always_comb begin
        dup_add = 2'd0;
        if (st == S_OUT && aout_tvalid && aout_tready) begin
            if (prev_valid && (o0 == prev_val))
                dup_add = dup_add + 2'd1;
            if (o1 == o0)
                dup_add = dup_add + 2'd1;
        end
    end

    // Odd-Even Sort
    always_comb begin
        for (int i = 0; i < N; i = i + 1)
            mem_next[i] = mem[i];

        if (st == S_SORT && pass < N) begin
            for (int i = 0; i < N-1; i = i + 1) begin
                if (i[0] == pass[0]) begin
                    logic [ELEM_W-1:0] a_tmp, b_tmp;
                    a_tmp = mem[i];
                    b_tmp = mem[i+1];

                    if (sort_dir_lat) begin
                        if (a_tmp > b_tmp) begin
                            mem_next[i]   = b_tmp;
                            mem_next[i+1] = a_tmp;
                        end
                    end
                    else begin
                        if (a_tmp < b_tmp) begin
                            mem_next[i]   = b_tmp;
                            mem_next[i+1] = a_tmp;
                        end
                    end
                end
            end
        end
    end


    always_ff @(posedge clk) begin
        if (rst) begin
            st           <= S_IDLE;
            in_b         <= '0;
            out_b        <= '0;
            pass         <= '0;
            sort_dir_lat <= 1'b0;
            dup_cnt      <= 32'd0;
            prev_val     <= '0;
            prev_valid   <= 1'b0;

            for (int i = 0; i < N; i = i + 1)
                mem[i] <= '0;
        end
        else begin
            case (st)
                S_IDLE: begin
                    in_b       <= '0;
                    out_b      <= '0;
                    pass       <= '0;
                    dup_cnt    <= 32'd0;
                    prev_valid <= 1'b0;
                    if (ain_tvalid)
                        st <= S_LOAD;
                end

                S_LOAD: begin
                    if (ain_tvalid && ain_tready) begin
                        if (in_b == '0)
                            sort_dir_lat <= sort_dir;

                        mem[in_idx0] <= ain_tdata[15:0];
                        mem[in_idx1] <= ain_tdata[31:16];

                        if (in_b == (BEATS[BTW-1:0] - 1'b1)) begin
                            in_b <= '0;
                            pass <= '0;
                            st   <= S_SORT;
                        end
                        else begin
                            in_b <= in_b + 1'b1;
                        end
                    end
                end

                S_SORT: begin
                    for (int i = 0; i < N; i = i + 1)
                        mem[i] <= mem_next[i];

                    if (pass == N) begin
                        out_b      <= '0;
                        dup_cnt    <= 32'd0;
                        prev_valid <= 1'b0;
                        st         <= S_OUT;
                    end
                    else begin
                        pass <= pass + 1'b1;
                    end
                end

                S_OUT: begin
                    if (aout_tvalid && aout_tready) begin
                        dup_cnt <= dup_cnt + {30'd0, dup_add};
                        prev_val   <= o1;
                        prev_valid <= 1'b1;

                        if (out_b == (BEATS[BTW-1:0] - 1'b1))
                            st <= S_IDLE;
                        else
                            out_b <= out_b + 1'b1;
                    end
                end

                default: st <= S_IDLE;
            endcase
        end
    end
endmodule


module sort_ip_sva #(
    parameter int N = 8
)(
    input logic clk,
    input logic rst,

    input logic        aout_tvalid,
    input logic        aout_tready,
    input logic [31:0] aout_tdata,
    input logic        aout_tlast,

    input logic        sort_dir,
    input logic [31:0] dup_nums
);

    localparam int ELEM_W = 16;
    localparam int BEATS  = N / 2;
    localparam int BTW    = (BEATS <= 1) ? 1 : $clog2(BEATS);

    logic [ELEM_W-1:0] out_arr [0:N-1];
    logic [BTW-1:0]    ob;

    logic frame_done, frame_done_q;
    logic sort_dir_cap, got_dir;

    logic [31:0]       dup_ref;
    logic [ELEM_W-1:0] prev_ref;
    logic              prev_ref_valid;
    

    logic [1:0] dup_add_ref_comb;
    always_comb begin
        dup_add_ref_comb = 2'd0;
        if (aout_tvalid && aout_tready && !frame_done) begin
            if (prev_ref_valid && (aout_tdata[15:0] == prev_ref))
                dup_add_ref_comb = dup_add_ref_comb + 2'd1;
            if (aout_tdata[31:16] == aout_tdata[15:0])
                dup_add_ref_comb = dup_add_ref_comb + 2'd1;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            ob             <= '0;
            frame_done     <= 1'b0;
            frame_done_q   <= 1'b0;
            sort_dir_cap   <= 1'b0;
            got_dir        <= 1'b1; // Default 1
            dup_ref        <= 32'd0;
            prev_ref       <= '0;
            prev_ref_valid <= 1'b0;

            for (int i = 0; i < N; i = i + 1)
                out_arr[i] <= '0;
        end
        else begin
            frame_done_q <= frame_done;

            if (aout_tvalid && aout_tready && !frame_done) begin
                if (!got_dir) begin
                    sort_dir_cap <= sort_dir;
                    got_dir      <= 1'b1;
                end
                
                out_arr[{ob,1'b0}]     <= aout_tdata[15:0];
                out_arr[{ob,1'b0} + 1'b1] <= aout_tdata[31:16];
                
                dup_ref <= dup_ref + {30'd0, dup_add_ref_comb};
                prev_ref       <= aout_tdata[31:16];
                prev_ref_valid <= 1'b1;

                if (ob == (BEATS[BTW-1:0] - 1'b1))
                    frame_done <= 1'b1;
                else
                    ob <= ob + 1'b1;
            end
        end
    end


    assert property (@(posedge clk) disable iff (rst)
        (aout_tvalid && aout_tready && (ob != (BEATS[BTW-1:0] - 1'b1))) |-> !aout_tlast
    );

    assert property (@(posedge clk) disable iff (rst)
        (aout_tvalid && !aout_tready) |=> $stable(aout_tdata)
    );

    assert property (@(posedge clk) disable iff (rst)
        (aout_tvalid && !aout_tready) |=> $stable(aout_tlast)
    );

    assert property (@(posedge clk) disable iff (rst)
        (aout_tvalid && aout_tready && (ob == (BEATS[BTW-1:0] - 1'b1))) |-> aout_tlast
    );

    genvar k;
    generate
        for (k = 0; k < N-1; k = k + 1) begin : sort_check
            assert property (@(posedge clk) disable iff (rst)
                frame_done_q |-> (
                    sort_dir_cap ?
                        (out_arr[k] <= out_arr[k+1]) :
                        (out_arr[k] >= out_arr[k+1])
                )
            );
        end
    endgenerate

    property dup_match_after_last;
        @(posedge clk) disable iff (rst)
        (aout_tvalid && aout_tready && (ob == (BEATS[BTW-1:0] - 1'b1)))
        |-> ##1 (dup_nums == dup_ref);
    endproperty
    assert property (dup_match_after_last);
endmodule


module sort_ip_formal_top;
    localparam int N     = 8;
    localparam int BEATS = N / 2;

    logic clk, rst;
    logic        ain_tvalid;
    logic        ain_tready;
    logic [31:0] ain_tdata;
    logic        ain_tlast;
    logic        aout_tvalid;
    logic        aout_tready;
    logic [31:0] aout_tdata;
    logic        aout_tlast;
    logic        sort_dir = 1'b0;
    logic [31:0] dup_nums;

    assign aout_tready = 1'b1; 

    sort_ip #(.N(N)) dut (.*);
    sort_ip_sva #(.N(N)) u_sva (.*);

`ifdef FORMAL
    integer hb;
    always_ff @(posedge clk) begin
        if (rst) hb <= 0;
        else if (ain_tvalid && ain_tready && hb < BEATS)
            hb <= hb + 1;
    end

    assume property (@(posedge clk) disable iff (rst) (hb < BEATS) |-> ain_tvalid);
    assume property (@(posedge clk) disable iff (rst) (hb == BEATS) |-> !ain_tvalid);
    assume property (@(posedge clk) disable iff (rst) (ain_tvalid && ain_tready && (hb != (BEATS - 1))) |-> !ain_tlast);
    assume property (@(posedge clk) disable iff (rst) (ain_tvalid && ain_tready && (hb == (BEATS - 1))) |-> ain_tlast);
    assume property (@(posedge clk) disable iff (rst) $stable(sort_dir));


    assume property (@(posedge clk) disable iff (rst) (hb == 0 && ain_tvalid && ain_tready) |-> (ain_tdata == 32'h0025_0013));
    assume property (@(posedge clk) disable iff (rst) (hb == 1 && ain_tvalid && ain_tready) |-> (ain_tdata == 32'h0025_0033));
    assume property (@(posedge clk) disable iff (rst) (hb == 2 && ain_tvalid && ain_tready) |-> (ain_tdata == 32'h0010_0015));
    assume property (@(posedge clk) disable iff (rst) (hb == 3 && ain_tvalid && ain_tready) |-> (ain_tdata == 32'h0012_0012));
`endif
endmodule
