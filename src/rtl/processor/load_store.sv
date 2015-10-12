// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Load_store ( 
  input logic clk,
  input logic reset,

  Load_store_ctrl_if.load_store  ctrl,
  //Load_store_data_if.load_store  data,
  input Pu_types::Address        address,
  input Pu_types::Word           din,
  output Backend::Result_bus     result,
  Ram_if.client                  dmem,
  Int_sched_if.load_store        except
);

import Pu_types::*;
import Backend::*;


Load_mode  mode;
logic[1:0] baddr;
logic      unaligned;
logic      unaligned_d;
Word       in;
Word       out;
Word       out_exts;
logic[3:0] in_mask;
logic[1:0] in_sh;
logic[3:0] out_mask;
logic[1:0] out_sh;
logic[2:0] ready_ctr;
logic      return_dout_d;
logic      exts_d;
Address next_eff_addr, eff_addr;

assign dmem.en = ctrl.en;

assign dmem.we = ctrl.ls_we & ~unaligned;
assign dmem.data_w = in;

assign dmem.addr = address[(($left(dmem.addr)+2 > 31) ? 31 : ($left(dmem.addr)+2)) : 2];
assign next_eff_addr = address;



//---------------------------------------------------------------------------
// Detect unaligned write accesses
//---------------------------------------------------------------------------
always_comb
begin
  // default assignment
  unaligned = 1'b0;
  except.base_alignment = 1'b0;

  if( ctrl.en ) begin
    if( ctrl.ls_mode == Load_word && address[1:0] != 2'b0 ) begin
      unaligned = 1'b1;
      except.base_alignment = 1'b1;
    end else if( ctrl.ls_mode == Load_halfword && address[1:0] == 2'b11 ) begin
      unaligned = 1'b1;
      except.base_alignment = 1'b1;
    end else begin
      unaligned = 1'b0;
      except.base_alignment = 1'b0;
    end
  end
end

//---------------------------------------------------------------------------
// Enable individual bytes for writing
//---------------------------------------------------------------------------
always_comb
begin
//  unique case(ctrl.ls_mode)
//    Load_halfword:  dmem.be = 4'b0011;
//    Load_byte:      dmem.be = 4'b0001;
//    default:        dmem.be = 4'b1111;
//  endcase

  if( ctrl.ls_mode == Load_halfword ) begin
    unique case(address[1:0])
      2'b00:   dmem.be = 4'b1100;
      2'b01:   dmem.be = 4'b0110;
      2'b10:   dmem.be = 4'b0011;
      default: dmem.be = 4'b0000;
    endcase
  end else if( ctrl.ls_mode == Load_byte ) begin
    unique case(address[1:0])
      2'b00:   dmem.be = 4'b1000;
      2'b01:   dmem.be = 4'b0100;
      2'b10:   dmem.be = 4'b0010;
      2'b11:   dmem.be = 4'b0001;
      //default: dmem.be = 4'b0000;
      default: dmem.be = 4'bxxxx;
    endcase
  end else
    dmem.be = 4'b1111;
end
//---------------------------------------------------------------------------
// Align data to the right on the input to the memory
//---------------------------------------------------------------------------
Byte_rotm in_align
  ( .w(din),
    .sh(in_sh),
    .mask(in_mask),
    .y(in) );

always_comb
begin
  logic[1:0] bsel;
  
  bsel = address[1:0];

  if( ctrl.ls_mode == Load_byte )
    in_sh = ~(address[1:0]);
  else if( ctrl.ls_mode == Load_halfword ) begin
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
  bsel = address[1:0];

  in_mask = 4'b0;

  if( ctrl.ls_mode == Load_byte ) begin
    unique case(bsel)
      2'b00:   in_mask = 4'b1000;
      2'b01:   in_mask = 4'b0100;
      2'b10:   in_mask = 4'b0010;
      3'b11:   in_mask = 4'b0001;
      default: in_mask = 4'bxxxx;
    endcase
  end else if( ctrl.ls_mode == Load_halfword ) begin
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

//---------------------------------------------------------------------------
// Align data to the right on the output after the memory
//---------------------------------------------------------------------------
Byte_rotm out_align
  ( .w(dmem.data_r),
    .sh(out_sh),
    .mask(out_mask),
    .y(out) );

always_comb
begin
  if( mode == Load_byte ) begin
    unique case(baddr)
      2'b00:   out_sh = 2'b01;
      2'b01:   out_sh = 2'b10;
      2'b10:   out_sh = 2'b11;
      2'b11:   out_sh = 2'b00;
      default: out_sh = 2'bxx;
    endcase
  end else if( mode == Load_halfword ) begin
    unique case(baddr)
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
  unique case(mode)
    Load_null:     out_mask = 4'b0000;
    Load_byte:     out_mask = 4'b0001;
    Load_halfword: out_mask = 4'b0011;
    Load_word:     out_mask = 4'b1111;
    default:       out_mask = 4'bxxxx;
  endcase
end

assign out_exts = (exts_d == 1'b1) ? { {16{out[15]}}, out[15:0] } : out;

always_comb begin
  result.valid = 1'b1;
  result.res_b = '0;
  result.crf = '0;
  result.msr = '0;
  result.cout = 1'b0;

  if( return_dout_d )
    result.res_a = out_exts & ~{DWIDTH{unaligned_d}};
  else
    result.res_a = eff_addr;
end

always_ff @(posedge clk)
begin
  if( ctrl.keep_eff_addr )
    eff_addr <= next_eff_addr;

  return_dout_d <= ctrl.return_dout;
  exts_d <= ctrl.exts;
end


//---------------------------------------------------------------------------
// Delay ctrl.mode and the lower two bits of the address to have it available
// after the data was returned from mem
//---------------------------------------------------------------------------
always_ff @(posedge clk)
begin
  mode = ctrl.ls_mode;
  baddr = address[1:0];
  unaligned_d = unaligned;
end


endmodule


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
