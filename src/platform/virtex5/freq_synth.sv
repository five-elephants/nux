// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Freq_synth 
  #(// bus addressing configurations
    //parameter int BASE_ADDR   = 32'h0000_0000,
    //parameter int BASE_MASK   = 32'hffff_ffff,

    // clock generation configuration
    parameter int DCM_M = 1,
    parameter int DCM_D = 5,
    parameter int PLL_M = 10,
    parameter int PLL_D_FAST = 5,
    parameter int PLL_D_SLOW = 10,

    parameter real CLK_FROM_IBUFG_PERIOD_NS = 10.0 )

  ( input logic clk_from_ibufg, resetb_pin,
    output logic clk_out_pin, reset_out,
    Bus_if.slave bus );

//---------------------------------------------------------------------------
// Clock generation and frequency synthesis
//---------------------------------------------------------------------------

localparam int REG_SPACE_BIT = 16;

typedef logic[6:0] Drp_addr;
typedef logic[15:0] Drp_data;

typedef struct packed {
  logic[31:2] dummy;
  logic sel_fast;
  logic en_gen_clk;
} Control_reg;

typedef enum logic[3:0] {
  S_IDLE       = 4'b0001,
  S_CONFIG_DCM = 4'b0010,
  S_REG        = 4'b0100,
  S_DONE       = 4'b1000,
  S_UNDEF      = 4'bxxxx
} State;

wire clkfb;
wire clk_to_bufg;
wire clk_from_dcm;
wire pll_clk_fast;
wire pll_clk_slow;
wire gen_clk;

logic locked;
logic dcm_locked, pll_locked;
logic reset;
logic reset_sync;
logic reset_cond;

logic dcm_dclk;
Drp_addr dcm_daddr;
Drp_data dcm_di, dcm_do;
logic dcm_den;
logic dcm_dwe;
logic dcm_drdy;

State state;
logic wr_creg;

Control_reg creg;

/** Asynchronous reset synchronizer based on Cummings Paper */
always_ff @(posedge clk_from_ibufg or negedge resetb_pin)
  if( !resetb_pin )
    {reset, reset_sync} <= 2'b11;
  else
    {reset, reset_sync} <= {reset_sync, 1'b0};

DCM_ADV #(
  .CLKFX_MULTIPLY(DCM_M),
  .CLKFX_DIVIDE(DCM_D),
  .CLKIN_PERIOD(CLK_FROM_IBUFG_PERIOD_NS),
  .CLK_FEEDBACK("NONE")
) dcm (
  .CLKIN(clk_from_ibufg),
  .CLKFB(),
  .RST(reset),
  
  .PSINCDEC(1'b0),
  .PSEN(1'b0),
  .PSCLK(1'b1),
  
  .DADDR(dcm_daddr),
  .DI(dcm_di),
  .DWE(dcm_dwe),
  .DEN(dcm_den),
  .DCLK(dcm_dclk),
  .DO(dcm_do),
  .DRDY(dcm_drdy),

  .CLK0(),
  .CLK90(),
  .CLK180(),
  .CLK270(),
  .CLK2X(),
  .CLK2X180(),
  .CLKDV(),
  .CLKFX(clk_from_dcm),
  .CLKFX180(),
  .LOCKED(dcm_locked),
  .PSDONE()
);

PLL_BASE #(
  .CLKFBOUT_MULT(PLL_M),
  .CLKOUT0_DIVIDE(PLL_D_FAST),
  .CLKOUT1_DIVIDE(PLL_D_SLOW),
  .CLKIN_PERIOD(CLK_FROM_IBUFG_PERIOD_NS * (DCM_D/DCM_M))
) pll (
  .CLKIN(clk_from_dcm),
  .RST(reset),
  .CLKFBOUT(clkfb),
  .CLKFBIN(clkfb),
  .CLKOUT0(pll_clk_fast),
  .CLKOUT1(pll_clk_slow),
  .CLKOUT2(),
  .CLKOUT3(),
  .CLKOUT4(),
  .CLKOUT5(),
  .LOCKED(pll_locked)
);

BUFGCTRL clkmux (
  .I0(pll_clk_fast),
  .I1(pll_clk_slow),
  .O(gen_clk),
  .S0(~creg.sel_fast),
  .S1(creg.sel_fast),
  .CE0(creg.en_gen_clk),
  .CE1(creg.en_gen_clk),
  .IGNORE0(1'b0),
  .IGNORE1(1'b0)
);

ODDR clk_oddr (
  .C(gen_clk),
  .CE(1'b1),
  .D1(1'b1),
  .D2(1'b0),
  .R(reset),
  .S(1'b0),
  .Q(clk_out_pin)
);

assign reset_cond = ~pll_locked | ~dcm_locked | reset;

always_ff @(posedge gen_clk or posedge reset_cond)
  if( reset_cond )
    reset_out <= 1'b1;
  else
    reset_out <= 1'b0;


//---------------------------------------------------------------------------
// Programming logic
//---------------------------------------------------------------------------

//Bus_slave_terminator terminate_freq_synth(bus);

//assign 
  //creg.en_gen_clk = 1'b1,
  //creg.sel_fast = 1'b1;


/** state transitions */
always_ff @(posedge bus.Clk or negedge bus.MReset_n)
  if( !bus.MReset_n ) begin
    state <= S_IDLE; 
  end else begin
    unique case(state)
      S_IDLE: begin
        if( bus.MCmd == Bus::RD || bus.MCmd == Bus::WR )
          if( bus.MAddr[REG_SPACE_BIT] )
            state <= S_REG;
          else
            state <= S_CONFIG_DCM;
      end

      S_CONFIG_DCM: begin
        if( dcm_drdy )
          state <= S_DONE;
      end

      S_REG: begin
        if( bus.MRespAccept )
          state <= S_IDLE;
      end

      S_DONE: begin
        if( bus.MRespAccept )
          state <= S_IDLE;
      end

      default:
        state <= S_UNDEF;
    endcase
  end

/** output */
always_comb begin
  // default assignments
  dcm_den = 1'b0;
  dcm_dwe = 1'b0;
  dcm_daddr = bus.MAddr[$left(dcm_daddr):$right(dcm_daddr)];
  dcm_di = bus.MData[$left(dcm_di):$right(dcm_di)];
  bus.SData = 0;
  bus.SCmdAccept = 1'b0;
  bus.SDataAccept = 1'b0;
  bus.SResp = Bus::NULL;
  wr_creg = 1'b0;

  unique case(state)
    S_IDLE: begin
      bus.SCmdAccept = 1'b1;
      bus.SDataAccept = 1'b1;

      if( bus.MAddr[REG_SPACE_BIT] ) begin
        if( bus.MCmd == Bus::WR ) begin
          wr_creg = 1'b1;
        end
      end else begin
        if( bus.MCmd == Bus::RD ) begin
          dcm_den = 1'b1;
          dcm_dwe = 1'b0;
        end else if( bus.MCmd == Bus::WR ) begin
          dcm_den = 1'b1;
          dcm_dwe = 1'b1;
        end
      end
    end

    S_CONFIG_DCM: begin
    end

    S_REG: begin
      bus.SResp = Bus::DVA;
      bus.SData = creg;
    end

    S_DONE: begin
      bus.SResp = Bus::DVA;
      bus.SData[$left(dcm_do):$right(dcm_do)] = dcm_do;
    end

    default: begin
      bus.SCmdAccept = 1'bx;
      bus.SDataAccept = 1'bx;
      dcm_den = 1'bx;
      dcm_dwe = 1'bx;
    end
  endcase
end

always_ff @(posedge bus.Clk or negedge bus.MReset_n)
  if( !bus.MReset_n ) begin
    creg <= '0;
  end else begin
    if( wr_creg )
      creg <= bus.MData;
  end

assign dcm_dclk = bus.Clk;

endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:

