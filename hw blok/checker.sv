module axi_sort_checker #(
    parameter DATA_WIDTH = 32,
    parameter ARRAY_SIZE = 1024
) (
    input logic clk,
    input logic resetn,
    input logic sort_dir,
    input logic [DATA_WIDTH-1:0] ain_tdata,
    input logic ain_tvalid,
    input logic ain_tready,
    input logic ain_tlast,
    input logic [DATA_WIDTH-1:0] aout_tdata,
    input logic aout_tvalid,
    input logic aout_tready,
    input logic aout_tlast,
    input logic [15:0] dup_nums
);

    // Internal array to track output values
    logic [15:0] output_array [0:ARRAY_SIZE-1];
    integer write_ptr = 0;

    // Capture sorted output into `output_array`
    always_ff @(posedge clk or negedge resetn) begin
        if (!resetn) begin
            write_ptr <= 0;
        end else if (aout_tvalid && aout_tready) begin
            output_array[write_ptr] <= aout_tdata[15:0];
            output_array[write_ptr + 1] <= aout_tdata[31:16];
            write_ptr <= write_ptr + 2;
        end
    end

    // AXI handshake property
    property axi_handshake;
        @(posedge clk) ain_tvalid |-> ain_tready;
    endproperty
    assert property (axi_handshake) else $fatal("AXI handshake failed!");

    // Sorted output property
    property sorted_output;
        @(posedge clk) (aout_tvalid && aout_tready) |-> (sort_dir ?
            (aout_tdata[15:0] <= aout_tdata[31:16]) :
            (aout_tdata[15:0] >= aout_tdata[31:16]));
    endproperty
    assert property (sorted_output) else $fatal("Output is not sorted correctly!");

    // Check that the entire array is sorted
    property fully_sorted;
        @(posedge clk) aout_tlast |-> check_sorted_array();
    endproperty
    assert property (fully_sorted) else $fatal("Output array is not sorted!");

    // Correct duplicate count property
    property correct_duplicate_count;
        @(posedge clk) aout_tlast |-> (dup_nums == count_duplicates());
    endproperty
    assert property (correct_duplicate_count) else $fatal("Duplicate count mismatch!");

    // Helper function to check if the output array is sorted
    function automatic bit check_sorted_array();
        int i;
        check_sorted_array = 1;
        for (i = 0; i < write_ptr - 1; i = i + 1) begin
            if (sort_dir) begin
                if (output_array[i] > output_array[i + 1]) begin
                    check_sorted_array = 0;
                    break;
                end
            end else begin
                if (output_array[i] < output_array[i + 1]) begin
                    check_sorted_array = 0;
                    break;
                end
            end
        end
    endfunction

    // Helper function to count duplicates in the output array
    function automatic int count_duplicates();
        int i, duplicates;
        duplicates = 0;
        for (i = 0; i < write_ptr - 1; i = i + 1) begin
            if (output_array[i] == output_array[i + 1]) begin
                duplicates++;
            end
        end
        return duplicates;
    endfunction

endmodule

