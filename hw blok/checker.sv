`timescale 1ns/1ps

// =============================================================================
// 1. sort_ip – Hardware sorting block 
// =============================================================================
module sort_ip #(
  parameter int N = 1024
)(
  input logic clk,
  input logic rst,

  input logic ain_tvalid,
  output logic ain_tready,
  input logic [31:0] ain_tdata,
  input logic ain_tlast,

  output logic aout_tvalid,
  input logic aout_tready,
  output logic [31:0] aout_tdata,
  output logic aout_tlast,

  input logic sort_dir,
  output logic [31:0] dup_nums
);

  localparam int ELEM_W = 16;
  localparam int BEATS = N / 2;
  localparam int IDXW = $clog2(N);
  localparam int BTW = (BEATS <= 1) ? 1 : $clog2(BEATS);
  
  localparam logic [BTW-1:0] LAST_BEAT = BTW'(BEATS - 1);

  typedef enum logic [1:0] { S_IDLE, S_LOAD, S_SORT, S_OUT } state_t;
  state_t st;

  logic [ELEM_W-1:0] mem [0:N-1];
  logic [ELEM_W-1:0] mem_next [0:N-1];

  logic [BTW-1:0] in_b;
  logic [BTW-1:0] out_b;
  logic [$clog2(N+1)-1:0] pass;

  logic sort_dir_lat;

  logic [IDXW-1:0] in_idx0, in_idx1;
  logic [IDXW-1:0] out_idx0, out_idx1;

  logic [ELEM_W-1:0] o0, o1;

  logic [31:0] dup_cnt;
  logic [31:0] dup_latch;
  logic [1:0] dup_add;
  logic [ELEM_W-1:0] prev_val;
  logic prev_valid;

  // -------------------------------------------------------------------------
  // Combinational outputs
  // -------------------------------------------------------------------------
  always_comb begin
    ain_tready = (st == S_LOAD);
    aout_tvalid = (st == S_OUT);

    in_idx0 = IDXW'({in_b, 1'b0});
    in_idx1 = in_idx0 + 1'b1;
    out_idx0 = IDXW'({out_b, 1'b0});
    out_idx1 = out_idx0 + 1'b1;

    o0 = mem[out_idx0];
    o1 = mem[out_idx1];
    aout_tdata = {o1, o0};
  end

  assign aout_tlast = (st == S_OUT) && (out_b == LAST_BEAT);
  assign dup_nums = dup_latch;

  // -------------------------------------------------------------------------
  // Duplicate detection (combinational)
  // -------------------------------------------------------------------------
  always_comb begin
    dup_add = 2'd0;
    if (st == S_OUT && aout_tvalid && aout_tready) begin
      if (prev_valid && (o0 == prev_val))
        dup_add = dup_add + 2'd1;
      if (o1 == o0)
        dup_add = dup_add + 2'd1;
    end
  end

  // -------------------------------------------------------------------------
  // Odd-Even Transposition Sort 
  // -------------------------------------------------------------------------
  always_comb begin
    logic [ELEM_W-1:0] a_tmp, b_tmp; 

    for (int i = 0; i < N; i = i + 1)
      mem_next[i] = mem[i];

    if (st == S_SORT && pass < N) begin
      for (int i = 0; i < N-1; i = i + 1) begin
        if (i[0] == pass[0]) begin
          a_tmp = mem[i];
          b_tmp = mem[i+1];

          if (sort_dir_lat) begin // ascending
            if (a_tmp > b_tmp) begin
              mem_next[i]   = b_tmp;
              mem_next[i+1] = a_tmp;
            end
          end else begin // descending
            if (a_tmp < b_tmp) begin
              mem_next[i]   = b_tmp;
              mem_next[i+1] = a_tmp;
            end
          end
        end
      end
    end
  end

  // -------------------------------------------------------------------------
  // Sequential FSM
  // -------------------------------------------------------------------------
  always_ff @(posedge clk) begin
    if (rst) begin
      st           <= S_IDLE;
      in_b         <= '0;
      out_b        <= '0;
      pass         <= '0;
      sort_dir_lat <= 1'b0;
      dup_cnt      <= 32'd0;
      dup_latch    <= 32'd0;
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

            if (in_b == LAST_BEAT) begin
              in_b <= '0;
              pass <= '0;
              st   <= S_SORT;
            end else begin
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
          end else begin
            pass <= pass + 1'b1;
          end
        end

        S_OUT: begin
          if (aout_tvalid && aout_tready) begin
            dup_cnt    <= dup_cnt + {30'd0, dup_add};
            prev_val   <= o1;
            prev_valid <= 1'b1;

            if (out_b == LAST_BEAT) begin
              dup_latch <= dup_cnt + {30'd0, dup_add};
              st        <= S_IDLE;
            end else begin
              out_b <= out_b + 1'b1;
            end
          end
        end

        default: st <= S_IDLE;
      endcase
    end
  end

endmodule


// =============================================================================
// 2. sort_ip_sva – Formal verification checker
// =============================================================================
module sort_ip_sva #(
  parameter int N = 8
)(
  input logic clk,
  input logic rst,

  input logic aout_tvalid,
  input logic aout_tready,
  input logic [31:0] aout_tdata,
  input logic aout_tlast,

  input logic sort_dir,
  input logic [31:0] dup_nums
);

  localparam int ELEM_W = 16;
  localparam int BEATS = N / 2;
  localparam int BTW = (BEATS <= 1) ? 1 : $clog2(BEATS);
  localparam int SVA_IDXW = $clog2(N);
  
  localparam logic [BTW-1:0] LAST_BEAT = BTW'(BEATS - 1);

  logic [ELEM_W-1:0] out_arr [0:N-1];
  logic [BTW-1:0] ob;

  logic frame_done, frame_done_q;
  logic sort_dir_cap, got_dir;

  logic [31:0] dup_ref;
  logic [ELEM_W-1:0] prev_ref;
  logic prev_ref_valid;

  // -------------------------------------------------------------------------
  // Reference dup counter
  // -------------------------------------------------------------------------
  logic [1:0] dup_add_ref;
  always_comb begin
    dup_add_ref = 2'd0;
    if (aout_tvalid && aout_tready && !frame_done) begin
      if (prev_ref_valid && (aout_tdata[15:0] == prev_ref))
        dup_add_ref = dup_add_ref + 2'd1;
      if (aout_tdata[31:16] == aout_tdata[15:0])
        dup_add_ref = dup_add_ref + 2'd1;
    end
  end

  // -------------------------------------------------------------------------
  // Reference model sequential logic
  // -------------------------------------------------------------------------
  always_ff @(posedge clk) begin
    if (rst) begin
      ob             <= '0;
      frame_done     <= 1'b0;
      frame_done_q   <= 1'b0;
      sort_dir_cap   <= 1'b0;
      got_dir        <= 1'b0;
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

        out_arr[SVA_IDXW'({ob, 1'b0})]        <= aout_tdata[15:0];
        out_arr[SVA_IDXW'({ob, 1'b0}) + 1'b1] <= aout_tdata[31:16];

        dup_ref        <= dup_ref + {30'd0, dup_add_ref};
        prev_ref       <= aout_tdata[31:16];
        prev_ref_valid <= 1'b1;

        if (ob == LAST_BEAT)
          frame_done <= 1'b1;
        else
          ob <= ob + 1'b1;
      end
    end
  end

  // =========================================================================
  // ASSERT PROPERTIES – AXI-S Handshakes
  // =========================================================================

  AP_not_last_mid_beat:
  assert property (
    @(posedge clk) disable iff (rst)
    (aout_tvalid && aout_tready && (ob != LAST_BEAT)) |-> !aout_tlast
  );

  AP_data_stable_on_backpressure:
  assert property (
    @(posedge clk) disable iff (rst)
    (aout_tvalid && !aout_tready) |=> $stable(aout_tdata)
  );

  AP_tlast_stable_on_backpressure:
  assert property (
    @(posedge clk) disable iff (rst)
    (aout_tvalid && !aout_tready) |=> $stable(aout_tlast)
  );

  AP_tlast_on_final_beat:
  assert property (
    @(posedge clk) disable iff (rst)
    (aout_tvalid && aout_tready && (ob == LAST_BEAT)) |-> aout_tlast
  );

  // =========================================================================
  // ASSERT PROPERTIES – Sort order correctness
  // =========================================================================
  genvar k;
  generate
    for (k = 0; k < N-1; k = k + 1) begin : gen_sort_order
      AP_sort_order:
      assert property (
        @(posedge clk) disable iff (rst)
        frame_done_q |-> (
          sort_dir_cap ? (out_arr[k] <= out_arr[k+1]) : (out_arr[k] >= out_arr[k+1])
        )
      );
    end
  endgenerate

  // =========================================================================
  // ASSERT PROPERTY – Duplicate count correctness
  // =========================================================================
  property p_dup_count_match;
    @ (posedge clk) disable iff (rst)
    (aout_tvalid && aout_tready && (ob == LAST_BEAT)) |-> ##1 (dup_nums == dup_ref);
  endproperty

  AP_dup_count_match: assert property (p_dup_count_match);

  // =========================================================================
  // COVER PROPERTIES
  // =========================================================================
  CP_frame_done:            cover property (@(posedge clk) disable iff (rst) frame_done_q);
  CP_duplicate_found:        cover property (@(posedge clk) disable iff (rst) frame_done_q && (dup_nums >= 32'd1));
  CP_multiple_duplicates:    cover property (@(posedge clk) disable iff (rst) frame_done_q && (dup_nums >= 32'd2));
  CP_no_duplicates:          cover property (@(posedge clk) disable iff (rst) frame_done_q && (dup_nums == 32'd0));
  CP_output_backpressure:    cover property (@(posedge clk) disable iff (rst) aout_tvalid && !aout_tready);
  CP_sort_ascending_done:    cover property (@(posedge clk) disable iff (rst) frame_done_q && sort_dir_cap);
  CP_sort_descending_done:   cover property (@(posedge clk) disable iff (rst) frame_done_q && !sort_dir_cap);
  CP_backpressure_then_done: cover property (@(posedge clk) disable iff (rst) (aout_tvalid && !aout_tready) ##[1:$] frame_done_q);

endmodule


// =============================================================================
// 3. sort_ip_formal_top – Formal
// =============================================================================
module sort_ip_formal_top (
  input logic        clk,
  input logic        rst,
  input logic        ain_tvalid,
  input logic [31:0] ain_tdata,
  input logic        ain_tlast,
  input logic        aout_tready,
  input logic        sort_dir
);

  parameter int N = 8; 
  localparam int BEATS = N / 2;

  // Izlazi iz DUT-a ostaju interna logika
  logic        ain_tready;
  logic        aout_tvalid;
  logic [31:0] aout_tdata;
  logic        aout_tlast;
  logic [31:0] dup_nums;

  // Instanciranje hardverskog bloka (DUT)
  sort_ip #(.N(N)) dut (.*);

  // Instanciranje formalnih čekera (SVA)
  sort_ip_sva #(.N(N)) u_sva (.*);

`ifdef FORMAL
  // -------------------------------------------------------------------------
  // Interni formalni brojač taktova (Beats)
  // -------------------------------------------------------------------------
  logic [$clog2(BEATS+1)-1:0] hb;
  logic packet_done;

  always_ff @(posedge clk) begin
    if (rst) begin
      hb          <= '0;
      packet_done <= 1'b0;
    end else begin
      if (ain_tvalid && ain_tready) begin
        if (ain_tlast) begin
          hb          <= '0;
          packet_done <= 1'b1;
        end else begin
          hb          <= hb + 1'b1;
        end
      end
    end
  end

  // -------------------------------------------------------------------------
  // AXI-Stream Protokol - Pretpostavke (Assumptions)
  // -------------------------------------------------------------------------
  ASM_ain_tvalid_stable: assume property (
    @(posedge clk) disable iff (rst)
    (ain_tvalid && !ain_tready) |=> ain_tvalid
  );

  ASM_ain_tdata_stable: assume property (
    @(posedge clk) disable iff (rst)
    (ain_tvalid && !ain_tready) |=> $stable(ain_tdata)
  );

  ASM_ain_tlast_stable: assume property (
    @(posedge clk) disable iff (rst)
    (ain_tvalid && !ain_tready) |=> $stable(ain_tlast)
  );

  ASM_ain_tlast_correct: assume property (
    @(posedge clk) disable iff (rst)
    ain_tvalid |-> (ain_tlast == (hb == BEATS - 1))
  );

  ASM_single_packet_per_run: assume property (
    @(posedge clk) disable iff (rst)
    packet_done |-> !ain_tvalid
  );

  ASM_sort_dir_stable: assume property (
    @(posedge clk) disable iff (rst)
    $stable(sort_dir)
  );

  // -------------------------------------------------------------------------
  // Generisanje realnih podataka umesto samo nula 
  // -------------------------------------------------------------------------
  ASM_data_not_zero: assume property (
    @(posedge clk) disable iff (rst)
    ain_tvalid |-> (ain_tdata[15:0] > 16'd0 && ain_tdata[31:16] > 16'd0)
  );

  ASM_data_not_equal: assume property (
    @(posedge clk) disable iff (rst)
    ain_tvalid |-> (ain_tdata[15:0] != ain_tdata[31:16])
  );
  
  ASM_data_range: assume property (
    @(posedge clk) disable iff (rst)
    ain_tvalid |-> (ain_tdata[15:0] < 16'd1000 && ain_tdata[31:16] < 16'd1000)
  );

  
  CP_witness_real_sorting: cover property (
    @(posedge clk) disable iff (rst)
    u_sva.frame_done_q && (u_sva.out_arr[0] > 16'd10)
  );

`endif
endmodule
