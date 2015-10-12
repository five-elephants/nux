// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Bus_access
  #( parameter int QUEUE_DEPTH = 4,
    parameter bit BYTE_ENABLED = 1'b1,
    parameter int ISSUE_TO_WB_LATENCY = 4)
  ( input logic clk, reset,
    input logic en,
    input Pu_types::Reg_index gpr_dest,
    input Pu_types::Load_mode mode,
    input logic exts,
    input Pu_types::Address baddr,
    input Pu_types::Word wdata,
    input logic req,
    input logic we,
    output Pu_types::Word result,
    output logic result_valid,
    Bus_if.master iobus,
    Delayed_wb_if.fub delayed_wb,
    output logic except_alignment,
    output logic pipe_empty );

import Pu_types::*;


localparam int LATENCY = ISSUE_TO_WB_LATENCY - 1;
localparam int STALL_ON_FULL_LATENCY = 3;
localparam int num_bytes = $bits(Address) / 8;

//---------------------------------------------------------------------------
// Local types & signals
//---------------------------------------------------------------------------

typedef logic[clog2(LATENCY)-1:0] Shift_id;
typedef logic[num_bytes-1:0] Byte_en;

typedef struct packed {
  logic we;
  Byte_en be;
  Address addr;
  Word wdata;
  logic unaligned;
} Request;

typedef struct packed {
  Reg_index gpr;
  Frontend::Thread_id thread;
  logic wb_data;
  Load_mode mode;
  logic[1:0] byte_sel;
  logic exts;
  logic unaligned;
  Shift_id id;
} Retire;

typedef struct packed {
  logic valid;
  Shift_id id;
} Timed_retire;


logic eff_en;
logic requesting;
logic unaligned;

Address addr;
Word in;
logic[3:0] in_mask;
logic[1:0] in_sh;
Word       out;
logic[3:0] out_mask;
logic[1:0] out_sh;
Word       out_exts;

logic q_push, q_pop;
Request q_req_in;
Request q_req_out;
logic q_empty;
logic q_almost_full;
logic q_full;

logic q_ret_pop;
Retire q_ret_in;
Retire q_ret_out;
logic q_ret_empty;
logic q_ret_almost_full;
logic q_ret_full;

Bus::Ocp_resp resp;
Word resp_data;
logic resp_accept;
logic wb_req, next_wb_req;
logic addr_acked;

logic delay_q_full;
logic delay_wb;
logic delay_always;

logic delayed_i;

Reg_index gpr_dest_d;
Reg_index gpr_dest_addr_d;

Shift_id shift_id;
Timed_retire ret_shift_in;
Timed_retire ret_shift_out;
logic on_time;

//logic scheduled_wb[0:Frontend::ls_latency-2];


//---------------------------------------------------------------------------
// Local logic
//---------------------------------------------------------------------------

assign eff_en = en & req;
assign addr = {2'b00, baddr[$left(baddr):2]};

assign delay_q_full = q_almost_full | q_ret_almost_full;
assign except_alignment = unaligned;
assign pipe_empty = q_empty & q_ret_empty;


//always_ff @(posedge clk)
//begin
  //gpr_dest_d <= gpr_dest;
  //gpr_dest_addr_d <= gpr_dest_addr;
//end

assign gpr_dest_d = gpr_dest;

/** Shift register to mark scheduled write back slots to Fubm_ls for WAW
* detection */
//always_ff @(posedge clk or posedge reset)
  //if( reset ) begin
    //for(int i=0; i<$bits(scheduled_wb); i++)
      //scheduled_wb[i] <= 1'b0;
  //end else begin
    //scheduled_wb[0] <= q_push;
    
    //for(int i=1; i<$bits(scheduled_wb); i++)
      //scheduled_wb[i] <= scheduled_wb[i-1];
  //end

// XXX Reset synchronizer?
assign iobus.MReset_n = ~reset;

//---------------------------------------------------------------------------
// Detect unaligned write accesses
//---------------------------------------------------------------------------
always_comb
begin
  // default assignment
  unaligned = 1'b0;

  if( eff_en ) begin
    if( mode == Load_word && baddr[1:0] != 2'b0 ) begin
      unaligned = 1'b1;
    end else if( mode == Load_halfword && baddr[1:0] == 2'b11 ) begin
      unaligned = 1'b1;
    end else begin
      unaligned = 1'b0;
    end
  end
end

//---------------------------------------------------------------------------
// Data alignment for request
//---------------------------------------------------------------------------

// Enable individual bytes for writing
always_comb
begin
  if( mode == Load_halfword ) begin
    unique case(baddr[1:0])
      2'b00:   q_req_in.be = 4'b1100;
      2'b01:   q_req_in.be = 4'b0110;
      2'b10:   q_req_in.be = 4'b0011;
      default: q_req_in.be = 4'b0000;
    endcase
  end else if( mode == Load_byte ) begin
    unique case(baddr[1:0])
      2'b00:   q_req_in.be = 4'b1000;
      2'b01:   q_req_in.be = 4'b0100;
      2'b10:   q_req_in.be = 4'b0010;
      2'b11:   q_req_in.be = 4'b0001;
      default: q_req_in.be = 4'bxxxx;
    endcase
  end else
    q_req_in.be = 4'b1111;
end

// Align data to the right on the input to the memory
Byte_rotm in_align
  ( .w(wdata),
    .sh(in_sh),
    .mask(in_mask),
    .y(in) );

always_comb
begin
  logic[1:0] bsel;
  
  bsel = baddr[1:0];

  if( mode == Load_byte )
    in_sh = ~(baddr[1:0]);
  else if( mode == Load_halfword ) begin
    unique case(bsel)
      2'b00:   in_sh = 2'b10;
      2'b01:   in_sh = 2'b01;
      2'b10:   in_sh = 2'b00;
      2'b11:   in_sh = 2'b00;
      default: in_sh = 2'bxx;
    endcase
  end else
    in_sh = 2'b00;
end

always_comb
begin
  logic[1:0] bsel;
  bsel = baddr[1:0];

  in_mask = 4'b0;

  if( mode == Load_byte ) begin
    unique case(bsel)
      2'b00:   in_mask = 4'b1000;
      2'b01:   in_mask = 4'b0100;
      2'b10:   in_mask = 4'b0010;
      3'b11:   in_mask = 4'b0001;
      default: in_mask = 4'bxxxx;
    endcase
  end else if( mode == Load_halfword ) begin
    unique case(bsel)
      2'b00:   in_mask = 4'b1100;
      2'b01:   in_mask = 4'b0110;
      2'b10:   in_mask = 4'b0011;
      2'b11:   in_mask = 4'b0000;
      default: in_mask = 4'bxxxx;
    endcase
  end else
    in_mask = 4'b1111;
end


// FIFO input side
assign 
  q_req_in.we = we,
  q_req_in.addr = addr,
  q_req_in.wdata = in,
  q_req_in.unaligned = unaligned;
assign q_push = eff_en & ~q_full;

DW_fifo_s1_sf #(
  .width($bits(Request)),
  .depth(QUEUE_DEPTH),
  .ae_level(1),
  .af_level(STALL_ON_FULL_LATENCY),
  .err_mode(0),
  .rst_mode(2)   // async reset without FIFO memory
) req_queue (
  .clk(clk),
  .rst_n(~reset),
  .push_req_n(~q_push),
  .pop_req_n(~q_pop),
  .diag_n(1'b1),
  .data_in(q_req_in),
  .empty(q_empty),
  .almost_empty(),
  .half_full(),
  .almost_full(q_almost_full),
  .full(q_full),
  .error(),
  .data_out(q_req_out)
);

assign
  q_ret_in.gpr = gpr_dest_d,
  q_ret_in.thread = '0,    //XXX use thread ID
  q_ret_in.wb_data = ~we,
  q_ret_in.mode = mode,
  q_ret_in.byte_sel = baddr[1:0],
  q_ret_in.exts = exts,
  q_ret_in.unaligned = unaligned,
  q_ret_in.id = shift_id;

DW_fifo_s1_sf #(
  .width($bits(Retire)),
  .depth(QUEUE_DEPTH),
  .ae_level(1),
  .af_level(STALL_ON_FULL_LATENCY),
  .err_mode(0),
  .rst_mode(2)   // async reset without FIFO memory
) retire_queue (
  .clk(clk),
  .rst_n(~reset),
  .push_req_n(~q_push),
  .pop_req_n(~q_ret_pop),
  .diag_n(1'b1),
  .data_in(q_ret_in),
  .empty(q_ret_empty),
  .almost_empty(),
  .half_full(),
  .almost_full(q_ret_almost_full),
  .full(q_ret_full),
  .error(),
  .data_out(q_ret_out)
);


assign
  ret_shift_in.valid = q_push && !we,       //no write to memory means store -> write to register
  ret_shift_in.id = shift_id;

always_ff @(posedge clk or posedge reset)
  if( reset )
    shift_id <= 0;
  else begin
    if( q_push )
      shift_id <= shift_id + 1;
  end

Shift_reg #(
  .depth(LATENCY),
  .width($bits(Timed_retire))
) ret_shiftreg (
  .clk, .reset,
  .en(1'b1),
  .in(ret_shift_in),
  .out(ret_shift_out)
);


//---------------------------------------------------------------------------
// Request generation
//---------------------------------------------------------------------------

//assign q_pop = iobus.SCmdAccept;
assign q_pop = iobus.SCmdAccept | (!q_empty & q_req_out.unaligned);

always_comb begin
  // default assignment
  iobus.MCmd = Bus::IDLE;
  iobus.MAddr = q_req_out.addr;
  iobus.MData = q_req_out.wdata;
  if( BYTE_ENABLED )
    iobus.MByteEn = q_req_out.be;
  else
    iobus.MByteEn = '1;

  if( !q_empty && !q_req_out.unaligned ) begin
    if( q_req_out.we ) begin
      iobus.MCmd = Bus::WR;
    end else begin
      iobus.MCmd = Bus::RD;
    end
  end
end

//---------------------------------------------------------------------------
// Response retirement
//---------------------------------------------------------------------------

/** register output from bus */
always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    resp <= Bus::NULL;
    resp_data <= '0;
  end else begin
    if( resp_accept ) begin
      resp <= iobus.SResp;
      resp_data <= iobus.SData;
    end
  end

/** retire requests */
always_comb begin
  // default assignments
  resp_accept = 1'b1;
  delay_wb = 1'b0;
  next_wb_req = 1'b0;
  q_ret_pop = 1'b0;
  on_time = 1'b0;

  if( resp == Bus::DVA || q_ret_out.unaligned ) begin
    if( q_ret_out.wb_data && !q_ret_empty ) begin
      // if on time -> don't use delayed write-back
      /*if( !delayed_i && (q_ret_out.id == ret_shift_out.id) && ret_shift_out.valid ) begin
        q_ret_pop = 1'b1;
        on_time = 1'b1;
      end else begin*/
        resp_accept = 1'b0;
        delay_wb = 1'b1;

        //q_ret_pop = delayed_wb.wb_ack & wb_req;
        q_ret_pop = delayed_wb.wb_ack;
        resp_accept = q_ret_pop;

        //if( !delayed_wb.wb_ack )
          //next_wb_req = 1'b1;
        next_wb_req = 1'b1;
      //end
    end else if( !q_ret_empty ) begin
      q_ret_pop = 1'b1;
    end
  end
end

//---------------------------------------------------------------------------
// Align data to the right on the output after the memory
//---------------------------------------------------------------------------
Byte_rotm out_align
  ( .w(resp_data),
    .sh(out_sh),
    .mask(out_mask),
    .y(out) );

always_comb
begin
  if( q_ret_out.mode == Load_byte ) begin
    unique case(q_ret_out.byte_sel)
      2'b00:   out_sh = 2'b01;
      2'b01:   out_sh = 2'b10;
      2'b10:   out_sh = 2'b11;
      2'b11:   out_sh = 2'b00;
      default: out_sh = 2'bxx;
    endcase
  end else if( q_ret_out.mode == Load_halfword ) begin
    unique case(q_ret_out.byte_sel)
      2'b00:   out_sh = 2'b10;
      2'b01:   out_sh = 2'b11;
      2'b10:   out_sh = 2'b00;
      2'b11:   out_sh = 2'b00;
      default: out_sh = 2'bxx;
    endcase
  end else
    out_sh = 2'b00;
end

always_comb
begin
  unique case(q_ret_out.mode)
    Load_null:     out_mask = 4'b0000;
    Load_byte:     out_mask = 4'b0001;
    Load_halfword: out_mask = 4'b0011;
    Load_word:     out_mask = 4'b1111;
    default:       out_mask = 4'bxxxx;
  endcase
end

assign out_exts = (q_ret_out.exts == 1'b1) ? { {16{out[15]}}, out[15:0] } : out;

assign iobus.MRespAccept = resp_accept;
assign result = out_exts;
assign result_valid = wb_req | on_time;


//---------------------------------------------------------------------------
// Frontend control
//---------------------------------------------------------------------------

/** Delay the frontend */
//always_ff @(posedge clk or posedge reset)
  //if( reset ) begin
    //delayed_i <= 1'b0;
    //wb_req <= 1'b0;
    //delayed_wb.wb_dest <= '0;
    //delayed_wb.wb_dest_valid <= 1'b0;
    //delayed_wb.wb_cancel <= 1'b0;
  //end else begin
    //delayed_i <= delay_q_full | delay_wb;
    //wb_req <= next_wb_req;
    //if( !q_ret_empty ) begin
      //delayed_wb.wb_dest <= q_ret_out.gpr;
      //delayed_wb.wb_dest_valid <= q_ret_out.wb_data;
      //delayed_wb.wb_cancel <= q_ret_out.unaligned;
    //end else begin
      //delayed_wb.wb_dest <= '0;
      //delayed_wb.wb_dest_valid <= 1'b0;
      //delayed_wb.wb_cancel <= 1'b0;
    //end
  //end

always_comb begin
    //delayed_i = delay_q_full | delay_wb;
    delayed_i = delay_q_full;
    wb_req = next_wb_req;
    if( !q_ret_empty ) begin
      delayed_wb.wb_dest = q_ret_out.gpr;
      delayed_wb.wb_dest_valid = q_ret_out.wb_data;
      delayed_wb.wb_cancel = q_ret_out.unaligned;
    end else begin
      delayed_wb.wb_dest = '0;
      delayed_wb.wb_dest_valid = 1'b0;
      delayed_wb.wb_cancel = 1'b0;
    end
end


assign delayed_wb.delayed = delayed_i;
//assign delayed_wb.scheduled_wb = scheduled_wb[$right(scheduled_wb)];
assign delayed_wb.scheduled_wb = on_time;
//assign delayed_wb.wb_req = wb_req & ~delayed_wb.wb_ack;
assign delayed_wb.wb_req = wb_req;
assign delayed_wb.track_dest = gpr_dest_d;
assign delayed_wb.track_valid = q_push & ~we;

endmodule
	

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
