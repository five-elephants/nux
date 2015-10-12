// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_reservation_station
  #(parameter int NUM_ENTRIES = 4,
    parameter int NUM_OPERANDS = 3,
    parameter int CONTROL_WIDTH = 1,
    parameter Vector::Unit_id THIS_UNIT_ID = Vector::VU_ID_MADD)
  ( input logic clk, reset,
    // insertion of new instructions
    output logic full,
    output logic empty,
    input logic ready,
    input logic insert,
    input logic[CONTROL_WIDTH-1:0] control_in,
    input Vector::Operands operands,
    output Vector::Rs_ref insert_ref,
    // requesting access to VRF
    output logic vrf_req,
    input logic vrf_ack,
    // control info for VRF
    output Vector::Vrf_index vrf_addr,
    output logic vrf_en,
    output logic vrf_we,
    output Vector::Rs_ref vrf_ref,
    // monitor on result bus
    input Vector::Vrf_index vrf_wb_addr,
    input logic vrf_wb_en,
    input logic vrf_wb_we,
    input Vector::Rs_ref vrf_wb_ref,
    // VCR read access
    output logic vcr_read,
    input logic wb_vcr,
    // enable operand input register during operand fetch
    output logic reg_in_en[0:NUM_OPERANDS-1],
    // passing on operations to the datapath control logic
    output logic[CONTROL_WIDTH-1:0] control_out,
    output logic control_valid,
    output Pu_types::Word g,
    input logic result_avail,
    output logic stall );


  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------
 
  typedef struct {
    Vector::Operands operands;
    logic[CONTROL_WIDTH-1:0] cbits;
  } Entry;

  typedef struct packed {
    logic wrap;
    logic[$clog2(NUM_ENTRIES)-1:0] ptr;
  } Entry_ptr;

  typedef enum logic[3:0] {
    S_EX_IDLE  = 4'b0001,
    S_EX_REQ_A = 4'b0010,
    S_EX_REQ_B = 4'b0100,
    S_EX       = 4'b1000,
    S_EX_UNDEF = 4'bxxxx
  } Executer_state;

  typedef enum logic[1:0] {
    S_RET_IDLE  = 2'b01,
    S_RET_REQ   = 2'b10,
    S_RET_UNDEF = 2'bxx
  } Retire_state;


  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------
  
  Entry entries[0:NUM_ENTRIES-1];
  Entry_ptr ptr_execute, ptr_retire, ptr_insert; 
  Entry_ptr ptr_execute_plus;
  //logic empty;
  Executer_state ex_state;
  Retire_state ret_state;
  logic inc_ex_ptr;
  logic inc_ret_ptr;
  logic next_reg_in_en[0:NUM_OPERANDS-1];
  logic[CONTROL_WIDTH-1:0] next_control_out;
  logic next_control_valid;
  Pu_types::Word next_g;
  logic vrf_ex_en;
  logic vrf_ex_we;
  logic vrf_ex_req;
  logic vrf_ex_ack;
  Vector::Vrf_index vrf_ex_addr;
  logic vrf_ret_en;
  logic vrf_ret_we;
  logic vrf_ret_req;
  logic vrf_ret_ack;
  Vector::Vrf_index vrf_ret_addr;
  logic mark_valid[0:NUM_ENTRIES-1][0:NUM_OPERANDS-1];
  logic mark_vcr_valid[0:NUM_ENTRIES-1];
  

  //--------------------------------------------------------------------------------
  // Local functions
  //--------------------------------------------------------------------------------
  
  function automatic Entry_ptr increment_pointer(Entry_ptr x);
    Entry_ptr rv;

    rv = x;

    if( rv.ptr == NUM_ENTRIES-1 ) begin
      rv.ptr = 0;
      rv.wrap = ~rv.wrap;
    end else begin
      rv.ptr = rv.ptr +1;
    end

    return rv;
  endfunction

  function automatic bit compare_pointers(Entry_ptr a, b);
    if( (a.ptr == b.ptr) && (a.wrap == b.wrap) )
      return 1'b1;
    else
      return 1'b0;
  endfunction

  function automatic bit compare_pointers_wrapped(Entry_ptr a, b);
    if( (a.ptr == b.ptr) && (a.wrap != b.wrap) )
      return 1'b1;
    else
      return 1'b0;
  endfunction

  function automatic bit operands_ready(Entry_ptr a);
    if( (!entries[a.ptr].operands.required[0] || entries[a.ptr].operands.valid[0])
        && (!entries[a.ptr].operands.required[1] || entries[a.ptr].operands.valid[1])
        && (!entries[a.ptr].operands.require_vcr || entries[a.ptr].operands.vcr_valid) )
    begin
      return 1'b1;
    end else begin
      return 1'b0;
    end
  endfunction



  //--------------------------------------------------------------------------------
  // Some assignments
  //--------------------------------------------------------------------------------

  assign 
    insert_ref.unit = THIS_UNIT_ID,
    insert_ref.entry = ptr_insert.ptr;

  assign ptr_execute_plus = increment_pointer(ptr_execute);


  //--------------------------------------------------------------------------------
  // Insert new instructions
  //--------------------------------------------------------------------------------
 
  always_comb begin
    if( compare_pointers(ptr_insert, ptr_retire) 
        && compare_pointers(ptr_insert, ptr_execute) )
      empty = 1'b1;
    else
      empty = 1'b0;

    if( compare_pointers_wrapped(ptr_insert, ptr_retire) )
      full = 1'b1;
    else
      full = 1'b0;
  end


  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      //for(int i=0; i<NUM_ENTRIES; i++)
        //{>>{entries[i]}} <= {$bits(entries[i]){1'b0}};
      ptr_execute <= '0;
      ptr_retire <= '0;
      ptr_insert <= '0;
    end else begin
      // mark valid from listener
      for(int i=0; i<NUM_ENTRIES; i++) begin
        for(int j=0; j<NUM_OPERANDS; j++) begin
          if( mark_valid[i][j] )
            entries[i].operands.valid[j] <= 1'b1;
        end

        if( mark_vcr_valid[i] )
          entries[i].operands.vcr_valid <= 1'b1;
      end

      if( !full && insert ) begin
        entries[ptr_insert.ptr].operands <= operands;
        entries[ptr_insert.ptr].cbits <= control_in;
        ptr_insert <= increment_pointer(ptr_insert);
      end

      if( inc_ex_ptr )
        ptr_execute <= increment_pointer(ptr_execute);

      if( inc_ret_ptr )
        ptr_retire <= increment_pointer(ptr_retire);
    end


  //--------------------------------------------------------------------------------
  // Listen on wb bus for missing operands
  //--------------------------------------------------------------------------------
  
  generate
    genvar entry_i;
    for(entry_i=0; entry_i<NUM_ENTRIES; entry_i++) begin : gen_listen
      genvar operand_i;
      for(operand_i=0; operand_i<NUM_OPERANDS; operand_i++) begin : gen_op
      
        always_comb begin
          // default assignment
          mark_valid[entry_i][operand_i] = 1'b0;

          if( vrf_wb_en && vrf_wb_we && (vrf_wb_ref == entries[entry_i].operands.src_ref[operand_i]) )
            mark_valid[entry_i][operand_i] = 1'b1;
        end 

      end : gen_op

      always_comb begin
        mark_vcr_valid[entry_i] = wb_vcr;
      end

    end : gen_listen
  endgenerate



  //--------------------------------------------------------------------------------
  // execute instructions
  //--------------------------------------------------------------------------------
  

  always_ff @(posedge clk or posedge reset)
    if( reset )
      ex_state <= S_EX_IDLE;
    else
      unique case(ex_state)
        S_EX_IDLE: begin
          if( !compare_pointers(ptr_insert, ptr_execute)
              && ready
              && !stall
              && operands_ready(ptr_execute) )
          begin
            if( entries[ptr_execute.ptr].operands.required[0] )
              ex_state <= S_EX_REQ_A;
            else
              ex_state <= S_EX;
          end
        end

        S_EX_REQ_A: begin
          if( vrf_ex_ack ) begin
            if( entries[ptr_execute.ptr].operands.required[1] )
              ex_state <= S_EX_REQ_B;
            else
              ex_state <= S_EX;
          end
        end

        S_EX_REQ_B: begin
          if( vrf_ex_ack ) begin
            ex_state <= S_EX;
            //if( ready && !stall ) begin
              //if( !compare_pointers(ptr_insert, ptr_execute_plus)
                  //&& operands_ready(ptr_execute_plus) )
              //begin
                //if( entries[ptr_execute_plus.ptr].operands.required[0] )
                  //ex_state <= S_EX_REQ_A;
                //else
                  //ex_state <= S_EX;
              //end else begin
                //ex_state <= S_EX_IDLE;
              //end
            //end else
              //ex_state <= S_EX;
          end 
        end

        S_EX: begin
          if( ready && !stall ) begin
            ex_state <= S_EX_IDLE;
            /*if( !compare_pointers(ptr_insert, ptr_execute_plus)
                && operands_ready(ptr_execute_plus) )
            begin
              if( entries[ptr_execute_plus.ptr].operands.required[0] )
                ex_state <= S_EX_REQ_A;
              else
                ex_state <= S_EX;
            end*/
          end
        end

        default: begin
          ex_state <= S_EX_UNDEF;
        end
      endcase


  always_comb begin
    inc_ex_ptr = 1'b0;
    next_control_valid = 1'b0;
    next_control_out = Pu_inst::Xop_fxvmahm; 
    next_g = entries[ptr_execute.ptr].operands.g;
    vrf_ex_req = 1'b0;
    vrf_ex_addr = 'x;
    vrf_ex_en = 1'b0;
    vrf_ex_we = 1'b0;
    next_reg_in_en[0] = 1'b0;
    next_reg_in_en[1] = 1'b0;
    vcr_read = 1'b0;

    unique case(ex_state)
      S_EX_REQ_A: begin
        //vrf_ex_req = 1'b1;
        vrf_ex_req = ready;
        vrf_ex_addr = entries[ptr_execute.ptr].operands.src[0];
        vrf_ex_en = 1'b1;
        //next_reg_in_en[0] = 1'b1;
        next_reg_in_en[0] = vrf_ex_ack;
      end

      S_EX_REQ_B: begin
        //if( !stall) begin
        if( 1 ) begin 
          vrf_ex_req = 1'b1;
          //vrf_ex_req = ready;
          vrf_ex_addr = entries[ptr_execute.ptr].operands.src[1];
          vrf_ex_en = 1'b1;
          //next_reg_in_en[1] = 1'b1;
          next_reg_in_en[1] = vrf_ex_ack;

          /*if( vrf_ex_ack ) begin
            next_control_out = entries[ptr_execute.ptr].cbits;
            next_control_valid = 1'b1;
            vcr_read = entries[ptr_execute.ptr].operands.require_vcr;
            inc_ex_ptr = ready;
          end*/
        end
      end

      S_EX: begin
        if( !stall && ready ) begin
        //if( 1 ) begin
          next_control_out = entries[ptr_execute.ptr].cbits;
          next_control_valid = 1'b1;
          vcr_read = entries[ptr_execute.ptr].operands.require_vcr;
          inc_ex_ptr = 1'b1;
        end
      end

      default: begin
      end
    endcase
  end


  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      g <= '0;
      control_valid <= 1'b0;
      control_out <= Pu_inst::Xop_fxvmahm;
      for(int i=0; i<NUM_OPERANDS; i++)
        reg_in_en[i] <= 1'b0;
    end else begin
      if( !stall ) begin
        g <= next_g;
        control_valid <= next_control_valid;
        control_out <= next_control_out;
      end

      reg_in_en <= next_reg_in_en;
    end

  /*always_comb begin
    g = next_g;
    control_valid = next_control_valid;
    control_out = next_control_out;
    //reg_in_en = next_reg_in_en;
  end*/


  //--------------------------------------------------------------------------------
  // Retire state machine
  //--------------------------------------------------------------------------------
  
  always_ff @(posedge clk or posedge reset)
    if( reset )
      ret_state <= S_RET_IDLE;
    else
      unique case(ret_state)
        S_RET_IDLE: begin
          if( (result_avail && !vrf_ret_ack)
              && !compare_pointers(ptr_insert, ptr_retire)
              && entries[ptr_retire.ptr].operands.write_dest ) begin
            ret_state <= S_RET_REQ;
          end else if( result_avail
              && !compare_pointers(ptr_insert, ptr_retire)
              && !entries[ptr_retire.ptr].operands.write_dest ) begin
          end
        end

        S_RET_REQ: begin
          if( vrf_ret_ack )
            ret_state <= S_RET_IDLE;
        end

        default: begin
          ret_state <= S_RET_UNDEF;
        end
      endcase


  always_comb begin
    // default assignments
    inc_ret_ptr = 1'b0;
    vrf_ret_en = 1'b0;
    vrf_ret_we = 1'b1;
    vrf_ret_req = 1'b0;
    vrf_ret_addr = entries[ptr_retire.ptr].operands.dest;
    stall = 1'b0;

    unique case(ret_state)
      S_RET_IDLE: begin
        vrf_ret_req = result_avail & entries[ptr_retire.ptr].operands.write_dest;
        vrf_ret_en = result_avail & entries[ptr_retire.ptr].operands.write_dest;
        stall = (result_avail & entries[ptr_retire.ptr].operands.write_dest) && !vrf_ret_ack;
        //stall = (result_avail & entries[ptr_retire.ptr].operands.write_dest);

        if( result_avail && !entries[ptr_retire.ptr].operands.write_dest )
          inc_ret_ptr = 1'b1;
        else if( vrf_ret_ack )
          inc_ret_ptr = 1'b1;
      end

      S_RET_REQ: begin
        vrf_ret_en = 1'b1;
        vrf_ret_req = 1'b1;
        stall = !vrf_ret_ack;
        //stall = 1'b1;

        if( vrf_ret_ack )
          inc_ret_ptr = 1'b1;
      end

      default: begin
        inc_ret_ptr = 1'bx;
        vrf_ret_en = 1'bx;
        vrf_ret_we = 1'bx;
        vrf_ret_req = 1'bx;
        vrf_ret_addr = 'x;
        stall = 1'bx;
      end
    endcase
  end

  //--------------------------------------------------------------------------------
  // VRF handshake priority
  //--------------------------------------------------------------------------------
  
  always_comb begin
    // default assignments
    vrf_ret_ack = 1'b0;
    vrf_ex_ack = 1'b0;
    vrf_ref.unit = THIS_UNIT_ID;
    vrf_ref.entry = ptr_retire.ptr;

    if( vrf_ret_req ) begin
      vrf_en = vrf_ret_en;
      vrf_we = vrf_ret_we;
      vrf_addr = vrf_ret_addr;
      vrf_req = vrf_ret_req;
      vrf_ret_ack = vrf_ack;
    end else begin
      vrf_en = vrf_ex_en;
      vrf_we = vrf_ex_we;
      vrf_addr = vrf_ex_addr;
      vrf_req = vrf_ex_req;
      vrf_ex_ack = vrf_ack;
    end
  end


`ifndef SYNTHESIS

  initial assert($bits(insert_ref.entry) >= $bits(ptr_insert.ptr)) else
    $fatal("Rs_ref.entry to small for the configured number of entries.");

`endif  /* SYNTHESIS */

endmodule

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
