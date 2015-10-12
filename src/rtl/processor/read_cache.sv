// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



module Read_cache
  #(parameter int INDEX_SIZE = 3,
    parameter int DISPLACEMENT_SIZE = 2,
    parameter int TAG_SIZE = 7,
    parameter int WORD_SIZE = 32)
  ( input logic clk, reset,
    Bus_if.master fetch_bus,
    Ram_if.memory read_bus,
    
    Ram_if.client store_r,
    Ram_if.client store_w
  );

//---------------------------------------------------------------------------
// Local types and signals
//---------------------------------------------------------------------------

function automatic int clog2(input int x);
  int rv, y;
  y = 1;
  for(rv=0; y < x; rv++) begin 
    y = y * 2;
  end
  return rv;
  //return $clog2(x);
endfunction

localparam int NUM_ROWS = 2**INDEX_SIZE;
localparam int NUM_WORDS = 2**DISPLACEMENT_SIZE;

typedef logic[TAG_SIZE-1:0] Tag;
typedef logic[INDEX_SIZE-1:0] Index;
typedef logic[DISPLACEMENT_SIZE-1:0] Displacement;
typedef logic[WORD_SIZE-1:0] Word;

typedef struct packed {
  Tag tag;
  Index index;
  Displacement displ;
} C_addr;

typedef struct packed {
  logic line_valid;
  Displacement start;
  Displacement stop;
} C_valid;

typedef Word C_line[0:NUM_WORDS-1];

//enum logic[5:0] {
  //S_IDLE           = 6'b00_0001,
  //S_WRITE_FIRST    = 6'b00_0010,
  //S_REQ            = 6'b00_0100,
  //S_RESP           = 6'b00_1000,
  //S_WAIT_0         = 6'b01_0000,
  //S_WAIT_1         = 6'b10_0000,

  //S_UNDEF          = 6'bxx_xxxx
//} state;
enum logic[3:0] {
  S_IDLE           = 4'b0001,
  S_WRITE_FIRST    = 4'b0010,
  S_REQ            = 4'b0100,
  S_RESP           = 4'b1000,

  S_UNDEF          = 4'bxxxx
} state;


C_valid valids[0:NUM_ROWS-1];
Tag     tags[0:NUM_ROWS-1];

C_addr  addr, addr_d;
C_addr  fetch_addr;
logic   miss;
Tag     tag;
C_valid valid;
Tag     tag_w;
C_valid valid_w;
logic   we;
logic[0:NUM_WORDS-1] valid_mask;
logic[0:NUM_WORDS-1] valid_mask_a, valid_mask_b;

logic start_line_fetch;
logic requesting;
logic responding;
logic inc_req_cnt;
logic set_req_cnt;
logic inc_resp_cnt;
logic set_resp_cnt;
Displacement new_req_cnt;
Displacement req_cnt;
Displacement new_resp_cnt;
Displacement resp_cnt;
Displacement stop_cnt;
logic en_d;
logic miss_d;

//---------------------------------------------------------------------------
// Back fetching
//---------------------------------------------------------------------------

always_ff @(posedge clk or posedge reset)
  if( reset )
    state <= S_IDLE;
  else
    unique case(state)
      S_IDLE: begin
        if( miss )
          state <= S_WRITE_FIRST;
      end

      S_WRITE_FIRST: begin
        if( fetch_bus.SCmdAccept )
          state <= S_REQ;
      end

      S_REQ: begin
        if( (req_cnt == stop_cnt) && inc_req_cnt )
          state <= S_RESP;
      end

      S_RESP: begin
        if( (resp_cnt == stop_cnt) && inc_resp_cnt )
          //state <= S_WAIT_0;
          state <= S_IDLE;
      end

      //S_WAIT_0: begin
        //state <= S_WAIT_1;
      //end

      //S_WAIT_1: begin
        //state <= S_IDLE;
      //end

      default: begin
        state <= S_UNDEF;
      end
    endcase


always_comb begin
  // default assignments
  requesting = 1'b0;
  responding = 1'b0;
  start_line_fetch = 1'b0;

  unique case(state)
    S_IDLE: begin
      start_line_fetch = miss;
    end

    S_WRITE_FIRST: begin
      requesting = 1'b1;
      responding = 1'b1;
    end

    S_REQ: begin
      requesting = 1'b1;
      responding = 1'b1;
    end

    S_RESP: begin
      responding = 1'b1;
    end

    //S_WAIT_0, S_WAIT_1: begin
    //end

    default: begin
    end
  endcase
end


//
// datapath
//

always_comb begin
  new_req_cnt = addr_d.displ;
  set_req_cnt = start_line_fetch;
  inc_req_cnt = 1'b0;

  if( requesting && (fetch_bus.SCmdAccept == 1'b1) )
    inc_req_cnt = 1'b1;
end


always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    req_cnt <= 0;
  end else begin
    if( set_req_cnt )
      req_cnt <= new_req_cnt;
    else if( inc_req_cnt )
      req_cnt <= (req_cnt == NUM_WORDS-1) ? 0 : (req_cnt + 1);
  end


always_comb begin
  new_resp_cnt = addr_d.displ;
  set_resp_cnt = start_line_fetch;
  inc_resp_cnt = 1'b0;

  if( responding && (fetch_bus.SResp == Bus::DVA) )
    inc_resp_cnt = 1'b1;
end

always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    resp_cnt <= 0;
  end else begin
    if( set_resp_cnt )
      resp_cnt <= new_resp_cnt;
    else if( inc_resp_cnt )
      resp_cnt <= (resp_cnt == NUM_WORDS-1) ? 0 : (resp_cnt + 1);
  end


/** Remember stop value for line counters */
always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    stop_cnt <= 0;
    fetch_addr <= '0;
  end else begin
    if( start_line_fetch ) begin
      stop_cnt <= (addr_d.displ == 0) ? (NUM_WORDS-1) : (addr_d.displ - 1);
      fetch_addr <= addr_d;
    end
  end

/* bus request generation */
assign
  fetch_bus.MData = '0,
  fetch_bus.MReset_n = ~reset;

always_comb begin
  // default assignment
  fetch_bus.MCmd = Bus::IDLE;
  fetch_bus.MAddr = '0;
  fetch_bus.MByteEn = '1;
  fetch_bus.MRespAccept = 1'b0;

  if( requesting ) begin
    fetch_bus.MCmd = Bus::RD;
    fetch_bus.MAddr = {fetch_addr.tag, fetch_addr.index, req_cnt};
    fetch_bus.MByteEn = '1;
  end

  if( responding ) begin
    fetch_bus.MRespAccept = 1'b1;
  end
end

/* cache store writing */
always_comb begin
  store_w.en = 1'b0;
  store_w.we = 1'b0;
  store_w.be = '1;
  store_w.addr = {fetch_addr.index, resp_cnt};
  store_w.data_w = fetch_bus.SData;
  tag_w = fetch_addr.tag;
  valid_w.start = fetch_addr.displ;
  valid_w.stop = resp_cnt;
  valid_w.line_valid = 1'b1;
  we = 1'b0;

  if( responding ) begin
    //store_w.en = 1'b1;

    if( fetch_bus.SResp == Bus::DVA ) begin
      store_w.en = 1'b1;
      store_w.we = 1'b1;
      we = 1'b1;
    end
  end
end


//---------------------------------------------------------------------------
// Front read-out datapath
//---------------------------------------------------------------------------

assign addr = read_bus.addr[$bits(addr)-1:0];

assign read_bus.delay = miss;

assign
  store_r.en = read_bus.en & ~miss,
  store_r.addr = {addr.index, addr.displ},
  read_bus.data_r = store_r.data_r;

assign 
  store_r.we = '0,
  store_r.be = '1,
  store_r.data_w = '0;

/** Tag register bank */
always_ff @(posedge clk)
begin
  if( read_bus.en ) begin
    tag <= tags[addr.index];
  end

  if( we ) begin
    tags[fetch_addr.index] <= tag_w;
  end

  addr_d <= addr;
end

/** Valid register bank */
always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    for(int i=0; i<NUM_ROWS; i++) begin
      valids[i] <= 'b0;
    end
  end else begin
    if( read_bus.en )
      //if( we )
        //valid <= valid_w;
      //else
        valid <= valids[addr.index];

    if( we ) begin
      valids[fetch_addr.index] <= valid_w;
    end
  end

always_ff @(posedge clk or posedge reset)
  if( reset ) begin
    en_d <= 1'b0;
    miss_d <= 1'b0;
  end else begin
    en_d <= read_bus.en;
    miss_d <= miss;
  end

// same code as in rotm.sv:
/** Generate mask from one-hot coded start and stop bits */
generate
  genvar j;
  for(j=0; j<NUM_WORDS; j++) begin : gen_mask
    assign valid_mask[j] = ((| valid_mask_a[0:j]) & (| valid_mask_a[j:NUM_WORDS-1])) 
        | ((| valid_mask_b[0:j]) & (| valid_mask_b[j:NUM_WORDS-1]));
  end
endgenerate
//---------------------------------------------------------------------------
/** Generate "one-hot" start and stop signals a and b */
always_comb
begin : one_hot
  valid_mask_a = '0;
  valid_mask_b = '0;

  if( valid.start <= valid.stop ) begin
    valid_mask_a[valid.start] = 1'b1;
    valid_mask_a[valid.stop] = 1'b1;
  end else begin
    valid_mask_a[valid.start] = 1'b1;
    valid_mask_a[NUM_WORDS-1] = 1'b1;
    valid_mask_b[0] = 1'b1;
    valid_mask_b[valid.stop] = 1'b1;
  end
end : one_hot

/** miss detection
* (written in a funny way so 'x in tag won't hurt in simulation) */
always_comb begin
  // default assignment
  miss = 1'b0;

  if( en_d ) begin
    if( !valid.line_valid )
      miss = 1'b1;
    else if( (tag != addr_d.tag) || !valid_mask[addr_d.displ] )
      miss = 1'b1;
  end else begin
    miss = miss_d;
  end
end

`ifndef SYNTHESIS

  check_cache_store_no_delay: assert property (
    @(posedge clk) disable iff(reset)
    ( store_r.delay == 1'b0 && store_w.delay == 1'b0 )
  ) else
    $error("Cache store may not raise delay");

  check_read_bus: assert property (
    @(posedge clk) disable iff(reset)
    ( !read_bus.en |=> ($stable(read_bus.data_r) && $stable(read_bus.delay)) )
  ) else
    $error("Cache must hold data_r and delay stable if not enabled");

`endif

endmodule

// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
