// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_ls_shared
  #(parameter int NUM_SLICES = 1,
    parameter int NUM_ELEMS = 8,
    parameter int ELEM_SIZE = 16,
    parameter int SCALAR_SIZE = 32)
  ( input logic clk, reset,
    Vector_ls_ctrl_if.shared ctrl,
    Bus_if.master bus,
    output logic[SCALAR_SIZE-1:0] load_out,
    input logic[SCALAR_SIZE-1:0] store_serial_in);


  import Pu_types::Word;


  localparam int VECTOR_SIZE = NUM_ELEMS * ELEM_SIZE;
  localparam int SCALARS_PER_VECTOR = VECTOR_SIZE / SCALAR_SIZE;
  localparam int NUM_SCALARS = SCALARS_PER_VECTOR * NUM_SLICES;
  localparam int SCALAR_IN_VECTOR_SELECT_WIDTH = $clog2(SCALARS_PER_VECTOR);

  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------

  typedef logic[SCALAR_SIZE-1:0] Scalar;
  typedef logic[$clog2(NUM_SCALARS):0] Scalar_counter;

  typedef enum logic {
    S_IDLE   = 1'b0,
    S_ACTIVE = 1'b1,
    S_UNDEF  = 1'bx
  } State;

  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------
  
  State state;
  Word base_addr;
  Scalar_counter count;
  Scalar_counter req_counter, next_req_counter;
  Scalar_counter resp_counter, next_resp_counter;
  Bus::Ocp_cmd bus_cmd;

  //--------------------------------------------------------------------------------
  // Bus access
  //--------------------------------------------------------------------------------
 
  assign bus.MReset_n = ~reset;

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      state <= S_IDLE;
      base_addr <= '0;
      count <= 0;
      req_counter <= 0;
      resp_counter <= 0;
      bus_cmd <= Bus::RD;
    end else begin
      if( ctrl.new_op ) begin
        state <= S_ACTIVE;
        base_addr <= ctrl.g >> 2;
        count <= ctrl.count;
        req_counter <= 0;
        resp_counter <= 0;
        if( ctrl.we )
          bus_cmd <= Bus::WR;
        else
          bus_cmd <= Bus::RD;
      end else begin
        req_counter <= next_req_counter;
        resp_counter <= next_resp_counter;

        if( resp_counter == count )
          state <= S_IDLE;
      end
    end

  always_comb begin : bus_data_connections
    bus.MByteEn = '1;
    bus.MAddr = base_addr + req_counter;
    bus.MData = store_serial_in;
    load_out = bus.SData;
  end

  always_comb begin : issue_bus_requests
    // default assignments
    next_req_counter = req_counter;
    bus.MCmd = Bus::IDLE;
    ctrl.sel_store_word = req_counter[SCALAR_IN_VECTOR_SELECT_WIDTH-1:0];
    for(int i=0; i<$bits(ctrl.serial_output); i++)
      ctrl.serial_output[i] = 1'b0;

    if( (state == S_ACTIVE) && (req_counter != count) ) begin
      bus.MCmd = bus_cmd;
      //ctrl.serial_output[req_counter[$left(req_counter)-1 : SCALAR_IN_VECTOR_SELECT_WIDTH]] = 1'b1;
      ctrl.serial_output[req_counter[$left(req_counter) : SCALAR_IN_VECTOR_SELECT_WIDTH]] = 1'b1;
      
      if( bus.SCmdAccept )
        next_req_counter = req_counter + 1;
    end
  end


  always_comb begin : receive_bus_responses
    // default assignments
    next_resp_counter = resp_counter;
    bus.MRespAccept = 1'b0;
    ctrl.sel_word = resp_counter[SCALAR_IN_VECTOR_SELECT_WIDTH-1:0];
    for(int i=0; i<$bits(ctrl.load_en); i++)
      ctrl.load_en[i] = 1'b0;

    if( (state == S_ACTIVE) && (resp_counter != count) ) begin
      bus.MRespAccept = 1'b1;

      if( bus.SResp == Bus::DVA ) begin
        next_resp_counter = resp_counter + 1;
        //ctrl.load_en[resp_counter[$left(resp_counter)-1 : SCALAR_IN_VECTOR_SELECT_WIDTH]] = 1'b1;
        ctrl.load_en[resp_counter[$left(resp_counter) : SCALAR_IN_VECTOR_SELECT_WIDTH]] = 1'b1;
      end
    end
  end


  always_comb begin : signal_completion_to_control
    if( (state == S_ACTIVE) && (resp_counter == count) )
      ctrl.complete = 1'b1;
    else
      ctrl.complete = 1'b0;
  end

endmodule
