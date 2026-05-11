`timescale 1ns/1ps

module panex #(
    parameter int S = 4
)(
    input  logic clk,
    input  logic rst,
    input  logic [1:0] fr,
    input  logic [1:0] to,
    output logic done
);

    localparam logic [1:0] L = 2'b00;
    localparam logic [1:0] M = 2'b01;
    localparam logic [1:0] R = 2'b10;
    localparam int N = 2 * S;

    logic [1:0] pos [N];
    logic [7:0] lvl [N];

    logic [7:0] top_lvl [3];
    logic [7:0] top_idx [3];

    logic       cross_occ [3];
    logic [7:0] cross_idx [3];

    always_comb begin
        for (int p = 0; p < 3; p++) begin
            top_lvl[p]   = 8'(S + 1);
            top_idx[p]   = 8'(N);
            cross_occ[p] = 1'b0;
            cross_idx[p] = 8'(N);
        end
        for (int i = 0; i < N; i++) begin
            if (lvl[i] == 0) begin
                cross_occ[pos[i]] = 1'b1;
                cross_idx[pos[i]] = 8'(i);
            end else if (lvl[i] < top_lvl[pos[i]]) begin
                top_lvl[pos[i]] = lvl[i];
                top_idx[pos[i]] = 8'(i);
            end
        end
    end

    logic       mv_legal;
    logic [7:0] moving_disk;
    logic [7:0] disk_limit;
    logic [7:0] target_lvl;
    logic       path_clear;
    logic [7:0] avail_depth;

    always_comb begin
        mv_legal    = 1'b0;
        moving_disk = 8'(N);
        disk_limit  = 8'd0;
        target_lvl  = 8'd0;
        path_clear  = 1'b0;
        avail_depth = 8'd0;

        if (cross_occ[fr])
            moving_disk = cross_idx[fr];
        else if (top_idx[fr] != 8'(N))
            moving_disk = top_idx[fr];

        if (moving_disk != 8'(N) && fr != to) begin
            disk_limit = (moving_disk < 8'(S))
                         ? (moving_disk + 8'd1)
                         : (moving_disk - 8'(S) + 8'd1);

            if ((fr == L && to == R) || (fr == R && to == L)) begin
                if (!cross_occ[M] && !cross_occ[to]) path_clear = 1'b1;
            end else begin
                if (!cross_occ[to]) path_clear = 1'b1;
            end

            if (path_clear) begin
                avail_depth = top_lvl[to] - 8'd1;

                if (avail_depth < disk_limit)
                    target_lvl = avail_depth;
                else
                    target_lvl = disk_limit;

                mv_legal = 1'b1;
            end
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i = 0; i < N; i++) begin
                pos[i] <= (i < S) ? L : R;
                lvl[i] <= (i < S) ? 8'(i + 1) : 8'(i - S + 1);
            end
        end else if (mv_legal) begin
            pos[moving_disk] <= to;
            lvl[moving_disk] <= target_lvl;
        end
    end

    always_comb begin
        done = 1'b1;
        for (int i = 0; i < N; i++) begin
            logic [1:0] next_pos;
            logic [7:0] next_lvl;

            next_pos = (mv_legal && moving_disk == 8'(i)) ? to : pos[i];
            next_lvl = (mv_legal && moving_disk == 8'(i)) ? target_lvl : lvl[i];

            if (i < S) begin
                if (next_pos != R || next_lvl != 8'(i + 1))
                    done = 1'b0;
            end else begin
                if (next_pos != L || next_lvl != 8'(i - S + 1))
                    done = 1'b0;
            end
        end
    end

    assume_legal:  assume property (@(posedge clk) disable iff (rst) mv_legal);
    assume_inputs: assume property (@(posedge clk) disable iff (rst)
                       fr inside {L,M,R} && to inside {L,M,R} && fr != to);

    cover_done: cover property (@(posedge clk) disable iff (rst) done);

endmodule
