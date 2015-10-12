// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Vector_pls_ctrl
  #(parameter int ELEM_SIZE = 16,
    parameter int NUM_ELEMS = 8)
  ( input logic clk, reset,
    input logic valid,
    input Pu_inst::Fxv_opcd xo,
    input Pu_inst::Fxv_cond cond,
    output logic result_avail,
    input logic stall,
    Vector_pls_ctrl_if.ctrl ctrl,
    output logic ready,
    input Pu_types::Word g );


  localparam int BYTE_EN_WIDTH = (NUM_ELEMS*ELEM_SIZE)/8;

  //--------------------------------------------------------------------------------
  // Local types
  //--------------------------------------------------------------------------------
  
  typedef enum logic {
    S_REQ_IDLE   = 1'b0,
    S_REQ_ACTIVE = 1'b1,
    S_REQ_UNDEF  = 1'bx
  } Request_state;


  //--------------------------------------------------------------------------------
  // Local signals
  //--------------------------------------------------------------------------------
  
  Request_state req_state;
  Bus::Ocp_cmd cmd;
  Pu_types::Word addr;
  Pu_inst::Fxv_cond cond_d;


  //--------------------------------------------------------------------------------
  // request generation
  //--------------------------------------------------------------------------------
  
  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      req_state <= S_REQ_IDLE;
    end else begin
      unique case(req_state)
        S_REQ_IDLE: begin
          if( valid && !stall )
            req_state <= S_REQ_ACTIVE;
        end

        S_REQ_ACTIVE: begin
          if( ctrl.SCmdAccept )
            req_state <= S_REQ_IDLE;
        end
      endcase
    end


  always_ff @(posedge clk) begin
    if( valid && (req_state == S_REQ_IDLE) ) begin
      if( xo == Pu_inst::Xop_fxvinx ) begin
        cmd <= Bus::RD;
        addr <= g;
        cond_d <= cond;
      end else if( xo == Pu_inst::Xop_fxvoutx ) begin
        cmd <= Bus::WR;
        addr <= g;
        cond_d <= cond;
      end
    end
  end
  
  always_comb begin
    // default assignments
    ready = 1'b1;
    ctrl.MAddr = addr;
    ctrl.MCmd = Bus::IDLE;
    ctrl.capture = 1'b0;
    ctrl.stored_byteen = 1'b0;
    ctrl.cond = cond_d;
    //ctrl.MByteEn = '1;

    unique case(req_state)
      S_REQ_IDLE: begin
        if( valid ) begin
          ctrl.capture = 1'b1;
        end
      end

      S_REQ_ACTIVE: begin
        ctrl.stored_byteen = 1'b1;
        ready = ctrl.SCmdAccept;
        ctrl.MCmd = cmd;
      end

      default: begin
      end
    endcase
  end


  //--------------------------------------------------------------------------------
  // response generation
  //--------------------------------------------------------------------------------

  always_ff @(posedge clk or posedge reset)
    if( reset ) begin
      result_avail <= 1'b0;
    end else begin
      if( result_avail ) begin
        if( !stall ) begin
          result_avail <= 1'b0;
        end
      end else begin
        if( ctrl.SResp == Bus::DVA )
          result_avail <= 1'b1;
      end
    end

  assign ctrl.MRespAccept = result_avail & ~stall;


endmodule

