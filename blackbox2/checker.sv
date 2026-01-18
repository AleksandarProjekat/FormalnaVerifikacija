checker v_bb_model_checker (
    CLK,
     RST,
     STALL,
     REQ,
    ACK,
     OPCH,
     DONE,
     ERR,
     OPS,
     TEST,
     AB,
     BC,
     CD,
     BUSY,
     DATA
);

    default clocking @(posedge CLK);
    endclocking

    default disable iff (RST);

    // Assert: Every REQ must have a corresponding ACK
    property req_ack_correspondence;
        disable iff (RST)
        REQ |-> ##[1:10] ACK; 
    endproperty
    assert property(req_ack_correspondence) else $error("REQ without ACK detected");

    // Assert: While there are pending REQs, BUSY is active
    property pending_reqs_busy;
        disable iff (RST)
        (REQ && !ACK) |-> BUSY;
    endproperty
    assert property(pending_reqs_busy) else $error("BUSY inactive while REQs are pending");

    // Assert: DONE is asserted for exactly one cycle after the last ACK
    property done_single_cycle_after_ack;
        disable iff (RST)
        (ACK && !$past(REQ)) ##1 (DONE && !$stable(DONE)) ##1 !DONE;
    endproperty
    assert property(done_single_cycle_after_ack) else $error("DONE is not asserted correctly after ACK");

    // Assert: DATA is stable when DONE is asserted
    property data_stable_when_done;
        disable iff (RST)
        DONE |-> $stable(DATA);
    endproperty
    assert property(data_stable_when_done) else $error("DATA is not stable when DONE is asserted");

    // Assert: TEST triggers the AB -> BC -> CD sequence
    property test_sequence;
        disable iff (RST)
        TEST |-> (AB[*3] ##3 BC[*3] or AB[*3] ##4 BC[*4]) ##[1:10] CD; // Zamena [3:4]
    endproperty
    assert property(test_sequence) else $error("TEST sequence AB -> BC -> CD violated");

    // Assert: ERR is never active
    property no_error_signal;
        disable iff (RST)
        !ERR;
    endproperty
    assert property(no_error_signal) else $error("ERR is active");

    // Assert: OPS has at most 1 bit set
    property ops_single_bit_set;
        disable iff (RST)
        $countones(OPS) <= 1;
    endproperty
    assert property(ops_single_bit_set) else $error("OPS has invalid bit pattern");

    // Assert: OPS does not change during STALL
    property ops_no_change_during_stall;
        disable iff (RST)
        STALL |-> !$changed(OPS);
    endproperty
    assert property(ops_no_change_during_stall) else $error("OPS changed during STALL");

    // Cover: OPS transitions from 4'b0100 to 4'b0101 after 4 cycles
    property ops_transition_cover;
        disable iff (RST)
        (OPS == 4'b0100) ##4 (OPS == 4'b0101);
    endproperty
    cover property(ops_transition_cover);

    // Cover: Sequence of AB -> BC -> CD is observed
    property ab_bc_cd_cover;
        disable iff (RST)
        (AB[*3] ##3 BC[*3] or AB[*3] ##4 BC[*4]) ##[1:10] CD; // Zamena [3:4]
    endproperty
    cover property(ab_bc_cd_cover);

endchecker

