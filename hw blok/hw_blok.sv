module sort_ip #(
    parameter DATA_WIDTH = 32,
    parameter ARRAY_SIZE = 1024
) (
    input wire clk,
    input wire resetn,

    // AXI Stream input
    input wire [DATA_WIDTH-1:0] ain_tdata,
    input wire ain_tvalid,
    output reg ain_tready,
    input wire ain_tlast,

    // AXI Stream output
    output reg [DATA_WIDTH-1:0] aout_tdata,
    output reg aout_tvalid,
    input wire aout_tready,
    output reg aout_tlast,

    // Control signals
    input wire sort_dir, // 1 for ascending, 0 for descending
    output reg [15:0] dup_nums
);

    // Internal storage
    reg [15:0] array [0:ARRAY_SIZE-1];
    reg [15:0] count;
    reg [15:0] write_ptr;
    reg [15:0] read_ptr;

    reg processing;

    // States for FSM
    typedef enum logic [2:0] {
        IDLE,
        RECEIVE,
        SORT,
        OUTPUT
    } state_t;

    state_t current_state, next_state;

    // Input processing
    always_ff @(posedge clk or negedge resetn) begin
        if (!resetn) begin
            current_state <= IDLE;
            ain_tready <= 0;
            write_ptr <= 0;
            read_ptr <= 0;
            processing <= 0;
            count <= 0;
            dup_nums <= 0;
            aout_tvalid <= 0;
            aout_tlast <= 0;
        end else begin
            current_state <= next_state;

            case (current_state)
                IDLE: begin
                    ain_tready <= 1;
                    aout_tvalid <= 0;
                    aout_tlast <= 0;
                    if (ain_tvalid) begin
                        next_state <= RECEIVE;
                    end
                end

                RECEIVE: begin
                    if (ain_tvalid && ain_tready) begin
                        array[write_ptr] <= ain_tdata[15:0];
                        array[write_ptr + 1] <= ain_tdata[31:16];
                        write_ptr <= write_ptr + 2;

                        if (ain_tlast || write_ptr >= ARRAY_SIZE - 2) begin
                            count <= write_ptr;
                            ain_tready <= 0;
                            next_state <= SORT;
                        end
                    end
                end

                SORT: begin
                    // Perform sorting
                    int i, j;
                    reg [15:0] temp;
                    reg [15:0] duplicate_count;
                    duplicate_count = 0;

                    for (i = 0; i < count - 1; i++) begin
                        for (j = 0; j < count - i - 1; j++) begin
                            if ((sort_dir && array[j] > array[j+1]) ||
                                (!sort_dir && array[j] < array[j+1])) begin
                                temp = array[j];
                                array[j] = array[j+1];
                                array[j+1] = temp;
                            end
                        end
                    end

                    // Count duplicates
                    for (i = 0; i < count - 1; i++) begin
                        if (array[i] == array[i+1]) begin
                            duplicate_count++;
                        end
                    end

                    dup_nums <= duplicate_count;
                    read_ptr <= 0;
                    next_state <= OUTPUT;
                end

                OUTPUT: begin
                    if (aout_tready) begin
                        aout_tdata <= {array[read_ptr + 1], array[read_ptr]};
                        aout_tvalid <= 1;
                        read_ptr <= read_ptr + 2;

                        if (read_ptr + 2 >= count) begin
                            aout_tlast <= 1;
                            next_state <= IDLE;
                        end else begin
                            aout_tlast <= 0;
                        end
                    end else begin
                        aout_tvalid <= 0;
                    end
                end

                default: begin
                    next_state <= IDLE;
                end
            endcase
        end
    end

endmodule

