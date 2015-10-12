// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Schedule_single
  ( input logic clk, reset,
    
    input Frontend::Frontend_control  ctrl,

    input Frontend::Fetch_state       fst,
    input Frontend::Branch_control    bctrl,
    input Frontend::Interrupt_control ictrl,
    input logic                       inst_ready,
    input Frontend::Predecoded        predec,
    input logic                       pipe_empty,

    input Frontend::Fub_readies       ready,
    output Frontend::Issue_array      issue_slots,

    output logic                      stall,
    output logic                      about_to_halt,
    output logic                      halted,
    output logic                      ignore_inst,
    output logic                      disable_wb,
    output logic                      csync,
    output logic                      jumping );

import Frontend::*;

//---------------------------------------------------------------------------
// Local signals and types
//---------------------------------------------------------------------------

typedef enum logic[7:0] {
  S_RESET        = 8'b0000_0001,
  S_FETCHING     = 8'b0000_0010,
  S_JUMPING      = 8'b0000_0100,
  S_HALTED       = 8'b0000_1000,
  S_SYNCING      = 8'b0001_0000,
  S_SYNC_TO_HALT = 8'b0010_0000,
  S_SYNC_JUMP_0  = 8'b0100_0000,
  S_SYNC_JUMP_1  = 8'b1000_0000,
  S_UNDEF        = 8'bxxxx_xxxx
} State;


State state;


//---------------------------------------------------------------------------
// Local functions
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
function automatic Issue_slot no_issue();
  Issue_slot rv;

  rv.valid = 1'b0;
  rv.pc = '0;
  rv.npc = '0;
  rv.ir = '0;
  rv.thread = '0;

  return rv;
endfunction
//---------------------------------------------------------------------------
//function automatic void issue(inout Issue_array issue_ar, logic stall);
  //int fub_id;
  
  //fub_id = fu_set_id(predec.fu_set); 
  //stall = 1'b0;

  //if( ready[fub_id] ) begin
    //issue_ar[fub_id].valid = 1'b1;
    //issue_ar[fub_id].ir = fst.inst;
    //issue_ar[fub_id].pc = fst.pc;
    //issue_ar[fub_id].npc = fst.npc;
  //end else
    //stall = 1'b1;

  //if( fst.predicted_taken ) begin
    //issue_ar[FUB_ID_BRANCH].valid = 1'b1;
    //issue_ar[FUB_ID_BRANCH].ir = fst.inst;
    //issue_ar[FUB_ID_BRANCH].pc = fst.pc;
    //issue_ar[FUB_ID_BRANCH].npc = fst.npc;
  //end
//endfunction
//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// Statemachine
//---------------------------------------------------------------------------

/** State transitions */
always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    state <= S_RESET;
  end else begin
    unique case(state)
      S_RESET: begin
        if( fst.valid )
          if( predec.halt )
            state <= S_SYNC_TO_HALT;
          else if( predec.context_sync )
            state <= S_SYNCING;
          else
            state <= S_FETCHING;
      end

      S_FETCHING: begin
        if( bctrl.jump )
          state <= S_JUMPING;
        else if( ictrl.jump )
          state <= S_SYNC_JUMP_0;
        else if( predec.halt )
          state <= S_SYNC_TO_HALT;
        else if( predec.context_sync )
          state <= S_SYNCING;
      end

      S_JUMPING: begin
        if( fst.trans_cmplt)
          if( predec.halt )
            state <= S_SYNC_TO_HALT;
          else if( ictrl.jump )
            state <= S_SYNC_JUMP_0;
          else if( predec.context_sync )
            state <= S_SYNCING;
          else
            state <= S_FETCHING;
      end

      S_HALTED: begin
        if( ctrl.wakeup )
          if( bctrl.jump )
            state <= S_JUMPING;
          else if( ictrl.jump )
            state <= S_SYNC_JUMP_0;
          else if( predec.context_sync )
            state <= S_SYNCING;
          else
            state <= S_FETCHING;
      end

      S_SYNCING: begin
        // signal from Inst_track, that all instructions have finished
        if( pipe_empty )
          state <= S_FETCHING;
      end

      S_SYNC_TO_HALT: begin
        if( bctrl.jump )
          state <= S_JUMPING;
        else if( fst.trans_cmplt )
          state <= S_FETCHING;
        else if( pipe_empty )
          state <= S_HALTED;
      end

      S_SYNC_JUMP_0: begin
        if( fst.trans_cmplt )
          state <= S_SYNC_JUMP_1;
      end

      S_SYNC_JUMP_1: begin
        if( pipe_empty )
          state <= S_FETCHING;
      end

      default:
        state <= S_UNDEF;
    endcase
  end


/** FSM outputs: scheduling logic */
always_comb begin
  // default assignments
  for(int i=0; i<FUB_ID_END; i++)
    issue_slots[i] = no_issue();
  stall = 1'b0;
  about_to_halt = 1'b0;
  halted = 1'b0;
  ignore_inst = 1'b0;
  csync = 1'b0;
  disable_wb = 1'b0;
  jumping = 1'b0;

  unique case(state)
    S_RESET: begin
      if( fst.valid ) begin
        if( !predec.halt && !predec.is_nop )
          // Design Compiler produces incorrect circuits when the function call is used here :-/
          //issue(issue_slots, stall);
        begin
          int unsigned fub_id;
          
          fub_id = fu_set_id(predec.fu_set); 
          stall = 1'b0;

          if( ready[fub_id] ) begin
            issue_slots[fub_id].valid = 1'b1;
            issue_slots[fub_id].ir = fst.inst;
            issue_slots[fub_id].pc = fst.pc;
            issue_slots[fub_id].npc = fst.npc;
          end else
            stall = 1'b1;

          if( fst.predicted_taken ) begin
            issue_slots[FUB_ID_BRANCH].valid = 1'b1;
            issue_slots[FUB_ID_BRANCH].ir = fst.inst;
            issue_slots[FUB_ID_BRANCH].pc = fst.pc;
            issue_slots[FUB_ID_BRANCH].npc = fst.npc;
          end
        end
      end else
        ignore_inst = 1'b1;
    end

    S_FETCHING: begin
      if( inst_ready && !bctrl.jump && !predec.halt && !predec.is_nop )
        //issue(issue_slots, stall);
        begin
          int unsigned fub_id;
          
          fub_id = fu_set_id(predec.fu_set); 
          stall = 1'b0;

          if( ready[fub_id] ) begin
            issue_slots[fub_id].valid = 1'b1;
            issue_slots[fub_id].ir = fst.inst;
            issue_slots[fub_id].pc = fst.pc;
            issue_slots[fub_id].npc = fst.npc;
          end else
            stall = 1'b1;

          if( fst.predicted_taken ) begin
            issue_slots[FUB_ID_BRANCH].valid = 1'b1;
            issue_slots[FUB_ID_BRANCH].ir = fst.inst;
            issue_slots[FUB_ID_BRANCH].pc = fst.pc;
            issue_slots[FUB_ID_BRANCH].npc = fst.npc;
          end
        end

      jumping = bctrl.jump;
    end

    S_JUMPING: begin
      if( fst.trans_cmplt && inst_ready && !predec.halt && !predec.is_nop )
        //issue(issue_slots, stall);
        begin
          int unsigned fub_id;
          
          fub_id = fu_set_id(predec.fu_set); 
          stall = 1'b0;

          if( ready[fub_id] ) begin
            issue_slots[fub_id].valid = 1'b1;
            issue_slots[fub_id].ir = fst.inst;
            issue_slots[fub_id].pc = fst.pc;
            issue_slots[fub_id].npc = fst.npc;
          end else
            stall = 1'b1;

          if( fst.predicted_taken ) begin
            issue_slots[FUB_ID_BRANCH].valid = 1'b1;
            issue_slots[FUB_ID_BRANCH].ir = fst.inst;
            issue_slots[FUB_ID_BRANCH].pc = fst.pc;
            issue_slots[FUB_ID_BRANCH].npc = fst.npc;
          end
        end
      
      ignore_inst = ~fst.trans_cmplt;
      jumping = 1'b1;
    end

    S_HALTED: begin
      stall = 1'b1;
      halted = 1'b1;
    end

    S_SYNCING: begin
      csync = 1'b1;
      stall = 1'b1;
    end

    S_SYNC_TO_HALT: begin
      stall = 1'b1;
      halted = 1'b0;
      about_to_halt = 1'b1;
      csync = 1'b1;  // I don't know if this is realy needed
    end

    S_SYNC_JUMP_0: begin
      csync = 1'b1;
      ignore_inst = ~fst.trans_cmplt;
      stall = fst.trans_cmplt;
      disable_wb = 1'b1;
    end

    S_SYNC_JUMP_1: begin
      csync = 1'b1;
      stall = 1'b1;
      disable_wb = 1'b1;
    end
      

    default: begin
      for(int i=0; i<FUB_ID_END; i++) begin
        issue_slots[i].valid = 1'bx;
        issue_slots[i].ir = 'x;
      end

      stall = 1'bx;
      about_to_halt = 1'bx;
      halted = 1'bx;
      ignore_inst = 1'bx;
      csync = 1'bx;
    end
  endcase
end
//---------------------------------------------------------------------------

endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
