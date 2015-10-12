// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


`ifndef VECTOR_PREDICTOR__
`define VECTOR_PREDICTOR__

`include "vector_instruction.sv"
`include "vector_state.sv"

import Valu_pkg::*;
import arithmetic::*;

class Vector_predictor
  #(int NUM_SLICES = 8,
    int NUM_ELEMS = 8,
    int ELEM_SIZE = 16,
    int VRF_SIZE = 32);

  typedef Vector_state #(NUM_SLICES, NUM_ELEMS, ELEM_SIZE, VRF_SIZE) My_vector_state;

  string msg;

  /** Predict resulting state of a vector instruction

  @param inst instruction
  @param state vector state
  @param pu_state state of the general purpose processor
  */
  function void predict(Vector_instruction inst,
      My_vector_state state,
      Sit::State pu_state);
    My_vector_state rv;

    if( inst.opcd != Pu_inst::Op_nve_xo )
      return;

    rv = state;

    msg = {msg, $sformatf("  <--- predicting  %s --->\n", inst.xo)};

    if( predict_byte(inst, state, pu_state) )
      return;

    if( predict_byte_fractional(inst, state, pu_state) )
      return;

    for(int slice_i=0; slice_i<NUM_SLICES; slice_i++) begin
      My_vector_state::Double_vector u, v, y, a, uf, vf;
      int ui[NUM_ELEMS], vi[NUM_ELEMS];
      My_vector_state::Vector_bytes bya;
      My_vector_state::Vector_bytes byb;
      My_vector_state::Vector_bytes byy;
      My_vector_state::Vector_bytes byt;

      Pu_types::Word gpr_a, gpr_b;

      gpr_a = pu_state.get_gpr(inst.ra);
      gpr_b = pu_state.get_gpr(inst.rb);

      for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
        u[elem_i] = sign_extend(state.vrf[slice_i][inst.ra][elem_i], VALU_TYPE_FULL);
        v[elem_i] = sign_extend(state.vrf[slice_i][inst.rb][elem_i], VALU_TYPE_FULL);
        uf[elem_i] = { state.vrf[slice_i][inst.ra][elem_i], {ELEM_SIZE{1'b0}} };
        vf[elem_i] = { state.vrf[slice_i][inst.rb][elem_i], {ELEM_SIZE{1'b0}} };
        ui[elem_i] = signed'(state.vrf[slice_i][inst.ra][elem_i]);
        vi[elem_i] = signed'(state.vrf[slice_i][inst.rb][elem_i]);
        a[elem_i] = state.accumulator[slice_i][elem_i];
      end

      bya = vector_to_bytes(state.vrf[slice_i][inst.ra]);
      byb = vector_to_bytes(state.vrf[slice_i][inst.rb]);
      byt = vector_to_bytes(state.vrf[slice_i][inst.rt]);

      case(inst.xo)
        Xop_fxvmtach: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            rv.accumulator[slice_i][elem_i] = mask_conditional_double(u[elem_i],
                rv.accumulator[slice_i][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
            msg = {msg, $sformatf("(slice_i=%2d, elem_i=%2d): ACC = %h\n",
                slice_i, elem_i, rv.accumulator[slice_i][elem_i])};
          end
        end

        Xop_fxvmtachf: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            rv.accumulator[slice_i][elem_i] = mask_conditional_double(uf[elem_i],
                rv.accumulator[slice_i][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
            msg = {msg, $sformatf("u[%2d] = %h ",
              elem_i, u[elem_i])};
            msg = {msg, $sformatf("(slice_i=%2d, elem_i=%2d): ACC = %h\n",
                slice_i, elem_i, rv.accumulator[slice_i][elem_i])};
          end
        end

        Xop_fxvmahm: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = u[elem_i] * v[elem_i] + a[elem_i];
            //$display("(slice=%2d, elem=%2d)  %h = %h * %h + %h",
              //slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i], a[elem_i]
            //);
            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                modulo_extract(y[elem_i], VALU_TYPE_FULL),
                state.vrf[slice_i][inst.rt][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
          end
        end

        Xop_fxvmahfs: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = mult_add_sat_fract(ui[elem_i], vi[elem_i], signed'(a[elem_i]), ELEM_SIZE);
            //y[elem_i] = add_sat(mult_sat_fract(ui[elem_i], vi[elem_i], ELEM_SIZE),
                //signed'(a[elem_i]), 2*ELEM_SIZE);
            msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h + %h",
                slice_i, elem_i, y[elem_i], uf[elem_i], vf[elem_i], a[elem_i])};

            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                saturating_fractional_extract(y[elem_i], 1, VALU_TYPE_FULL),
                state.vrf[slice_i][inst.rt][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
            msg = {msg, $sformatf("  VRF[%2d] = %h\n",
                inst.rt, rv.vrf[slice_i][inst.rt][elem_i])};
          end
        end

        Xop_fxvmatachm: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = u[elem_i] * v[elem_i] + a[elem_i];
            msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h + %h\n",
              slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i], a[elem_i]
            )};
            rv.accumulator[slice_i][elem_i] = mask_conditional_double(y[elem_i],
                rv.accumulator[slice_i][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
          end
        end

        Xop_fxvmatachfs: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = mult_add_sat_fract(ui[elem_i], vi[elem_i], signed'(a[elem_i]), ELEM_SIZE);
            msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h + %h",
                slice_i, elem_i, y[elem_i], ui[elem_i], vi[elem_i], signed'(a[elem_i]))};
            msg = {msg, $sformatf("  %h * %h = %h",
                ui[elem_i], vi[elem_i], mult_sat_fract(ui[elem_i], vi[elem_i], ELEM_SIZE))};

            //if( (u[elem_i][ELEM_SIZE-1:0] == {1'b1, {ELEM_SIZE-1{1'b0}}})
                //&& (v[elem_i][ELEM_SIZE-1:0] == {1'b1, {ELEM_SIZE-1{1'b0}}}) ) begin
              //y[elem_i] = {1'b0, {2*ELEM_SIZE-1{1'b1}}} + a[elem_i];
              //msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h + %h (saturating)\n",
                  //slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i], a[elem_i])};
            //end else begin
              ////y[elem_i] = ((u[elem_i] * v[elem_i]) << 1) + a[elem_i];
              //y[elem_i] = shift_left_saturating(u[elem_i] * v[elem_i], VALU_TYPE_FULL) + a[elem_i];
              //msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h + %h\n",
                  //slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i], a[elem_i])};
            //end

            rv.accumulator[slice_i][elem_i] = mask_conditional_double(
                y[elem_i],
                rv.accumulator[slice_i][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
            msg = {msg, $sformatf("  ACC = %h\n", rv.accumulator[slice_i][elem_i])};
          end
        end

        Xop_fxvmulhm: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = u[elem_i] * v[elem_i];
            //$display("(slice=%2d, elem=%2d)  %h = %h * %h + %h",
              //slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i], a[elem_i]
            //);
            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                modulo_extract(y[elem_i], VALU_TYPE_FULL),
                state.vrf[slice_i][inst.rt][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
          end
        end

        Xop_fxvmulhfs: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = mult_sat_fract(ui[elem_i], vi[elem_i], ELEM_SIZE);
            msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h + %h",
                slice_i, elem_i, y[elem_i], uf[elem_i], vf[elem_i], a[elem_i])};

            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                saturating_fractional_extract(y[elem_i], 1, VALU_TYPE_FULL),
                state.vrf[slice_i][inst.rt][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
            msg = {msg, $sformatf(" VRF[%2d] = %h\n",
                inst.rt, rv.vrf[slice_i][inst.rt][elem_i])};

            //if( (u[elem_i][ELEM_SIZE-1:0] == {1'b1, {ELEM_SIZE-1{1'b0}}})
                //&& (v[elem_i][ELEM_SIZE-1:0] == {1'b1, {ELEM_SIZE-1{1'b0}}}) )
            //begin
              //y[elem_i] = { {ELEM_SIZE{1'b0}}, 1'b0, {ELEM_SIZE-1{1'b1}} };

              //msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h\n",
                //slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i]
              //)};
              //rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                  //{ 1'b0, {ELEM_SIZE-1{1'b1}} },
                  //state.vrf[slice_i][inst.rt][elem_i],
                  //state.vcr[slice_i][elem_i],
                  //inst.cond);
              //msg = {msg, $sformatf(" VRF[%2d] = %h\n",
                  //inst.rt, rv.vrf[slice_i][inst.rt][elem_i])};
            //end
            //else
            //begin
              //y[elem_i] = shift_left_saturating(u[elem_i] * v[elem_i], VALU_TYPE_FULL);
              //msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h",
                //slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i]
              //)};
              //rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                  //saturating_fractional_extract(y[elem_i], 1, VALU_TYPE_FULL),
                  //state.vrf[slice_i][inst.rt][elem_i],
                  //state.vcr[slice_i][elem_i],
                  //inst.cond);
              //msg = {msg, $sformatf(" VRF[%2d] = %h\n",
                  //inst.rt, rv.vrf[slice_i][inst.rt][elem_i])};
            //end
          end
        end

        Xop_fxvmultachm: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = u[elem_i] * v[elem_i];
            //$display("(slice=%2d, elem=%2d)  %h = %h * %h + %h",
              //slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i], a[elem_i]
            //);
            rv.accumulator[slice_i][elem_i] = mask_conditional_double(y[elem_i],
                rv.accumulator[slice_i][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
          end
        end

        Xop_fxvmultachfs: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = mult_sat_fract(ui[elem_i], vi[elem_i], ELEM_SIZE);
            msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h + %h",
                slice_i, elem_i, y[elem_i], uf[elem_i], vf[elem_i], a[elem_i])};

            //if( (u[elem_i][ELEM_SIZE-1:0] == {1'b1, {ELEM_SIZE-1{1'b0}}})
                //&& (v[elem_i][ELEM_SIZE-1:0] == {1'b1, {ELEM_SIZE-1{1'b0}}}) ) begin
              //y[elem_i] = {1'b0, {2*ELEM_SIZE-1{1'b1}}};
              //msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h (saturating)\n",
                  //slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i])};
            //end else begin
              //y[elem_i] = shift_left_saturating(u[elem_i] * v[elem_i], VALU_TYPE_FULL);
              //msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h * %h\n",
                  //slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i])};
            //end

            rv.accumulator[slice_i][elem_i] = mask_conditional_double(y[elem_i],
                rv.accumulator[slice_i][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
            msg = {msg, $sformatf("ACC = %h\n", rv.accumulator[slice_i][elem_i])};
          end
        end

        Xop_fxvaddhm: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = u[elem_i] + v[elem_i];

            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                modulo_extract(y[elem_i], VALU_TYPE_FULL),
                state.vrf[slice_i][inst.rt][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
          end
        end

        Xop_fxvaddhfs: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = add_sat(ui[elem_i], vi[elem_i], ELEM_SIZE) << ELEM_SIZE;

            msg = {msg, $sformatf("(slice_i=%2d, elem_i=%2d) %h = %h + %h",
                slice_i, elem_i, y[elem_i], uf[elem_i], vf[elem_i])};

            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                saturating_fractional_extract(y[elem_i], 0, VALU_TYPE_FULL),
                state.vrf[slice_i][inst.rt][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);

            msg = {msg, $sformatf(" VRF[%2d] = %h\n",
                inst.rt, rv.vrf[slice_i][inst.rt][elem_i])};
          end
        end

        Xop_fxvaddtachm: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = u[elem_i] + v[elem_i];

            rv.accumulator[slice_i][elem_i] = mask_conditional_double(y[elem_i],
                rv.accumulator[slice_i][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
          end
        end

        Xop_fxvaddachm: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = u[elem_i] + a[elem_i];

            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                modulo_extract(y[elem_i], VALU_TYPE_FULL),
                state.vrf[slice_i][inst.rt][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
          end
        end

        Xop_fxvaddachfs: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            //y[elem_i] = uf[elem_i] + a[elem_i];
            y[elem_i] = add_sat(ui[elem_i] << ELEM_SIZE, signed'(a[elem_i]), 2*ELEM_SIZE);
            msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h + %h",
              slice_i, elem_i, y[elem_i], u[elem_i], a[elem_i]
            )};

            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                saturating_fractional_extract(y[elem_i], 0, VALU_TYPE_FULL),
                state.vrf[slice_i][inst.rt][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);

            msg = {msg, $sformatf(" VRF[%2d] = %h\n", inst.rt, rv.vrf[slice_i][inst.rt][elem_i])};
          end
        end

        Xop_fxvaddactachm: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = u[elem_i] + a[elem_i];

            rv.accumulator[slice_i][elem_i] = mask_conditional_double(y[elem_i],
                rv.accumulator[slice_i][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
          end
        end

        Xop_fxvaddactachf: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            //y[elem_i] = uf[elem_i] + a[elem_i];
            y[elem_i] = add_sat(ui[elem_i] << ELEM_SIZE, signed'(a[elem_i]), 2*ELEM_SIZE);

            msg = {msg, $sformatf("(slice_i=%2d, elem_i=%2d) %h = %h + %h",
                slice_i, elem_i, y[elem_i], uf[elem_i], a[elem_i])};

            rv.accumulator[slice_i][elem_i] = mask_conditional_double(y[elem_i],
                rv.accumulator[slice_i][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
            msg = {msg, $sformatf("  ACC=%h\n", rv.accumulator[slice_i][elem_i])};
          end
        end

        Xop_fxvsubhm: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = u[elem_i] - v[elem_i];
            //y[elem_i] = u[elem_i] + (~a[elem_i] + 1);

            //$display("(slice=%2d, elem=%2d)  %h = %h - %h",
              //slice_i, elem_i, y[elem_i], u[elem_i], v[elem_i]
            //);
            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                modulo_extract(y[elem_i], VALU_TYPE_FULL),
                state.vrf[slice_i][inst.rt][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);
          end
        end

        Xop_fxvsubhfs: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            y[elem_i] = add_sat(ui[elem_i], -vi[elem_i], ELEM_SIZE) << ELEM_SIZE;
            //y[elem_i] = uf[elem_i] - vf[elem_i];
            msg = {msg, $sformatf("(slice=%2d, elem=%2d)  %h = %h - %h",
              slice_i, elem_i, y[elem_i], uf[elem_i], vf[elem_i]
            )};

            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
                saturating_fractional_extract(y[elem_i], 0, VALU_TYPE_FULL),
                state.vrf[slice_i][inst.rt][elem_i],
                state.vcr[slice_i][elem_i],
                inst.cond);

            msg = {msg, $sformatf(" VRF[%2d] = %h\n", inst.rt, rv.vrf[slice_i][inst.rt][elem_i])};
          end
        end

        Xop_fxvcmph: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            int x;

            x = u[elem_i];

            rv.vcr[slice_i][elem_i].eq = {$bits(rv.vcr[slice_i][elem_i].eq){ (x == 0) }};
            rv.vcr[slice_i][elem_i].lt = {$bits(rv.vcr[slice_i][elem_i].lt){ (x < 0) }};
            rv.vcr[slice_i][elem_i].gt = {$bits(rv.vcr[slice_i][elem_i].gt){ (x > 0) }};
          end
        end

        Xop_fxvlax: begin
          My_vector_state::Vector_words wds;
          Pu_types::Address ea;

          ea = gpr_a + gpr_b + ((slice_i * My_vector_state::WORDS_PER_VECTOR) << 2);
          //$display("ea = %h (word address = %h)", ea, ea >> 2);

          for(int i=0; i<My_vector_state::WORDS_PER_VECTOR; ++i) begin
            wds[i] = pu_state.get_mem_model().get(ea[$left(ea):2]);
            ea += 4;
          end

          {>>{ rv.vrf[slice_i][inst.rt] }} = {>>{ wds }};
        end

        Xop_fxvstax: begin
          My_vector_state::Vector_words wds;
          Pu_types::Address ea;

          ea = gpr_a + gpr_b + ((slice_i * My_vector_state::WORDS_PER_VECTOR) << 2);
          //$display("ea = %h (word address = %h)", ea, ea >> 2);
          {>>{ wds }} = {>>{ state.vrf[slice_i][inst.rt] }};

          for(int i=0; i<My_vector_state::WORDS_PER_VECTOR; ++i) begin
            pu_state.get_mem_model().set(ea[$left(ea):2], wds[i]);
            ea += 4;
          end
        end

        Xop_fxvinx: begin
          Pu_types::Address ea;

          ea = gpr_a + gpr_b;

          msg = {msg, $sformatf("EA=%h", ea)};

          if( state.pmem.exists(ea) ) begin
            {>>{byt}} = state.pmem[ea][slice_i];
            msg = {msg, $sformatf(" EXISTS: %h\n", state.pmem[ea][slice_i])};
          end else begin
            {>>{byt}} = {NUM_ELEMS*ELEM_SIZE{1'b0}};
            state.pmem[ea] = {$bits(state.pmem[ea]){1'b0}};
            msg = {msg, $sformatf(" NEW: 0\n")};
          end


          for(int i=0; i<NUM_ELEMS; i++) begin
            logic[0:1] byteen;

            unique case(inst.cond)
              Pu_inst::Fxv_cond_null:  byteen = 2'b11;
              Pu_inst::Fxv_cond_gt:    byteen = {
                state.vcr[slice_i][i].gt[0] | state.vcr[slice_i][i].gt[1],
                state.vcr[slice_i][i].gt[2] | state.vcr[slice_i][i].gt[3]
              };
              Pu_inst::Fxv_cond_lt:    byteen = {
                state.vcr[slice_i][i].lt[0] | state.vcr[slice_i][i].lt[1],
                state.vcr[slice_i][i].lt[2] | state.vcr[slice_i][i].lt[3]
              };
              Pu_inst::Fxv_cond_eq:    byteen = {
                state.vcr[slice_i][i].eq[0] | state.vcr[slice_i][i].eq[1],
                state.vcr[slice_i][i].eq[2] | state.vcr[slice_i][i].eq[3]
              };
            endcase

            //$display(" elem=%2d, byteen=%b, cond=%h", i, byteen, inst.cond);
            if( byteen[0] ) begin
              byy[2*i] = byt[2*i];
              msg = {msg, $sformatf("  elem_i=%2d MSB enabled %h = %h\n",
                  i, byy[2*i], byt[2*i])};
            end else begin
              byy[2*i] = '0;
            end

            if( byteen[1] ) begin
              byy[2*i+1] = byt[2*i+1];
              msg = {msg, $sformatf("  elem_i=%2d LSB enabled %h = %h\n",
                  i, byy[2*i+1], byt[2*i+1])};
            end else begin
              byy[2*i+1] = '0;
            end
          end

          {>>{ rv.vrf[slice_i][inst.rt] }} = bytes_to_vector(byy);

          msg = {msg, $sformatf("  (slice_i=%2d) VRF[%2d] = %p, VCR=%p (=><), cond=%s\n",
              slice_i,
              inst.rt,
              rv.vrf[slice_i][inst.rt],
              state.vcr[slice_i],
              inst.cond)};
        end

        Xop_fxvoutx: begin
          Pu_types::Address ea;

          ea = gpr_a + gpr_b;

          msg = {msg, $sformatf("(slice_i=%2d)  EA=%h", slice_i, ea)};
          //for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            //state.pmem[ea][slice_i] = {>>{ rv.vrf[slice_i][inst.rt] }};
          //end

          if( state.pmem.exists(ea) ) begin
            {>>{byy}} = state.pmem[ea][slice_i];
            //$display("exists");
            msg = {msg, $sformatf(" EXISTS: %p\n", byy)};
          end else begin
            {>>{byy}} = {NUM_ELEMS*ELEM_SIZE{1'b0}};
            state.pmem[ea] = {$bits(state.pmem[ea]){1'b0}};
            msg = {msg, $sformatf(" NEW: %p\n", byy)};
            //$display("does not exist");
          end

          for(int i=0; i<NUM_ELEMS; i++) begin
            logic[0:1] byteen;

            unique case(inst.cond)
              Pu_inst::Fxv_cond_null:  byteen = 2'b11;
              Pu_inst::Fxv_cond_gt:    byteen = {
                state.vcr[slice_i][i].gt[0] | state.vcr[slice_i][i].gt[1],
                state.vcr[slice_i][i].gt[2] | state.vcr[slice_i][i].gt[3]
              };
              Pu_inst::Fxv_cond_lt:    byteen = {
                state.vcr[slice_i][i].lt[0] | state.vcr[slice_i][i].lt[1],
                state.vcr[slice_i][i].lt[2] | state.vcr[slice_i][i].lt[3]
              };
              Pu_inst::Fxv_cond_eq:    byteen = {
                state.vcr[slice_i][i].eq[0] | state.vcr[slice_i][i].eq[1],
                state.vcr[slice_i][i].eq[2] | state.vcr[slice_i][i].eq[3]
              };
            endcase

            //$display(" elem=%2d, byteen=%b, cond=%h", i, byteen, inst.cond);
            if( byteen[0] ) begin
              byy[2*i] = byt[2*i];
              msg = {msg, $sformatf("  elem_i=%2d MSB enabled\n", i)};
            end

            if( byteen[1] ) begin
              byy[2*i+1] = byt[2*i+1];
              msg = {msg, $sformatf("  elem_i=%2d LSB enabled\n", i)};
            end
          end

          //$display("slice_i=%2d", slice_i);
          //$display("VCR: %p", state.vcr[slice_i]);
          //$display("pre pmem = %h", {>>{state.pmem[ea][slice_i]}});
          //for(int j=0; j<My_vector_state::BYTES_PER_VECTOR; j++)
            //$display("byy[%2d] = %h",
              //j, byy[j]);
          rv.pmem[ea][slice_i] = {>>{ byy }};
          //$display("post pmem = %h", {>>{state.pmem[ea][slice_i]}});
          msg = {msg, $sformatf("  writing: %p\n", byy)};
        end

        Xop_fxvpckbu: begin
          int sz;

          sz = 8 - int'(inst.cond);
          msg = {msg, $sformatf("sz = %2d\n", sz)};
          for(int i=0; i<My_vector_state::BYTES_PER_VECTOR/2; i++) begin
            byy[i] = '0;
            byy[i + My_vector_state::BYTES_PER_VECTOR/2] = '0;

            for(int j=0; j<sz; j++) begin
              byy[i][sz-1-j] = bya[2*i][8-1-j];
              byy[i + My_vector_state::BYTES_PER_VECTOR/2][sz-1-j] = byb[2*i][8-1-j];
            end
          end

          rv.vrf[slice_i][inst.rt] = bytes_to_vector(byy);

          for(int j=0; j<My_vector_state::BYTES_PER_VECTOR; j++) begin
            msg = {msg,
              $sformatf("bya[%2d] = %h (%b)   ", j, bya[j], bya[j]),
              $sformatf("byb[%2d] = %h (%b)   ", j, byb[j], byb[j]),
              $sformatf("byy[%2d] = %h (%b)\n", j, byy[j], byy[j])
            };
          end
        end

        Xop_fxvpckbl: begin
          int sz;

          sz = 8 - int'(inst.cond);
          msg = {msg, $sformatf("sz = %2d\n", sz)};
          for(int i=0; i<My_vector_state::BYTES_PER_VECTOR/2; i++) begin
            byy[i] = '0;
            byy[i + My_vector_state::BYTES_PER_VECTOR/2] = '0;

            for(int j=0; j<8-sz; j++) begin
              byy[i][sz-1-j] = bya[2*i][8-sz-1-j];
              byy[i + My_vector_state::BYTES_PER_VECTOR/2][sz-1-j] = byb[2*i][8-sz-1-j];
            end

            for(int j=0; j<sz-(8-sz); j++) begin
              byy[i][sz-1-(8-sz)-j] = bya[2*i+1][8-1-j];
              byy[i + My_vector_state::BYTES_PER_VECTOR/2][sz-1-(8-sz)-j] = byb[2*i+1][8-1-j];
            end
          end

          rv.vrf[slice_i][inst.rt] = bytes_to_vector(byy);

          for(int j=0; j<My_vector_state::BYTES_PER_VECTOR; j++) begin
            msg = {msg,
              $sformatf("bya[%2d] = %h (%b)   ", j, bya[j], bya[j]),
              $sformatf("byb[%2d] = %h (%b)   ", j, byb[j], byb[j]),
              $sformatf("byy[%2d] = %h (%b)\n", j, byy[j], byy[j])
            };
          end
        end

        Xop_fxvupckbl: begin
          int sz;

          sz = 8 - int'(inst.cond);
          msg = {msg, $sformatf("sz = %2d\n", sz)};

          for(int i=0; i<My_vector_state::BYTES_PER_VECTOR/2; i++) begin
            byy[2*i] = '0;
            byy[2*i+1] = '0;

            for(int j=0; j<sz; j++) begin
              byy[2*i][7 - j] = bya[i][sz - 1 - j];
              //byy[2*i+1][7 - j] = byb[i][sz - 1 - j];
            end

            for(int j=0; j<sz; j++) begin
              if( j + sz < 8 )
                byy[2*i][7 - sz - j] = byb[i][sz - 1 - j];
              else
                byy[2*i+1][7 - (j - (8-sz))] = byb[i][sz - 1 - j];
            end
          end

          rv.vrf[slice_i][inst.rt] = bytes_to_vector(byy);

          for(int j=0; j<My_vector_state::BYTES_PER_VECTOR; j++) begin
            msg = {msg,
              $sformatf("bya[%2d] = %h (%b)   ", j, bya[j], bya[j]),
              $sformatf("byb[%2d] = %h (%b)   ", j, byb[j], byb[j]),
              $sformatf("byy[%2d] = %h (%b)\n", j, byy[j], byy[j])
            };
          end
        end

        Xop_fxvupckbr: begin
          int sz;

          sz = 8 - int'(inst.cond);
          msg = {msg, $sformatf("sz = %2d\n", sz)};

          for(int i=0; i<My_vector_state::BYTES_PER_VECTOR/2; i++) begin
            byy[2*i] = '0;
            byy[2*i+1] = '0;

            for(int j=0; j<sz; j++) begin
              byy[2*i][7 - j] = bya[i + My_vector_state::BYTES_PER_VECTOR/2][sz - 1 - j];
              //byy[2*i+1][7 - j] = byb[i][sz - 1 - j];
            end

            for(int j=0; j<sz; j++) begin
              if( j + sz < 8 )
                byy[2*i][7 - sz - j] = byb[i + My_vector_state::BYTES_PER_VECTOR/2][sz - 1 - j];
              else
                byy[2*i+1][7 - (j - (8-sz))] = byb[i + My_vector_state::BYTES_PER_VECTOR/2][sz - 1 - j];
            end
          end

          rv.vrf[slice_i][inst.rt] = bytes_to_vector(byy);

          for(int j=0; j<My_vector_state::BYTES_PER_VECTOR; j++) begin
            msg = {msg,
              $sformatf("bya[%2d] = %h (%b)   ", j, bya[j], bya[j]),
              $sformatf("byb[%2d] = %h (%b)   ", j, byb[j], byb[j]),
              $sformatf("byy[%2d] = %h (%b)\n", j, byy[j], byy[j])
            };
          end


          //for(int i=0; i<My_vector_state::BYTES_PER_VECTOR/2; i++) begin
            //byy[2*i] = bya[i + My_vector_state::BYTES_PER_VECTOR/2];
            //byy[2*i+1] = byb[i + My_vector_state::BYTES_PER_VECTOR/2];
          //end

          //rv.vrf[slice_i][inst.rt] = bytes_to_vector(byy);
        end

        Xop_fxvsplath: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            rv.vrf[slice_i][inst.rt][elem_i] = gpr_a[$bits(y[elem_i])-1 : 0];
          end

        end

        Xop_fxvshh: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            logic signed[4:0] shift_amount;

            shift_amount = inst.rb;

            msg = {msg,
              $sformatf("shift_amount = %2d, %h ->",
                shift_amount,
                state.vrf[slice_i][inst.ra][elem_i])
            };

            if( shift_amount < 0)
              rv.vrf[slice_i][inst.rt][elem_i] = state.vrf[slice_i][inst.ra][elem_i] >> -shift_amount;
            else
              rv.vrf[slice_i][inst.rt][elem_i] = state.vrf[slice_i][inst.ra][elem_i] << shift_amount;

            msg = {msg,
              $sformatf(" %h\n",
                rv.vrf[slice_i][inst.rt][elem_i])
            };
          end
        end

        Xop_fxvsel: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            msg = {msg,
              $sformatf("slice_i=%2d, elem_i=%2d: ",
                slice_i, elem_i),
              $sformatf("selecting between 0: %h and 1: %h (cond=%s|eq:%h, gt:%h, lt:%h) ->",
                state.vrf[slice_i][inst.ra][elem_i],
                state.vrf[slice_i][inst.rb][elem_i],
                inst.cond,
                state.vcr[slice_i][elem_i].eq,
                state.vcr[slice_i][elem_i].gt,
                state.vcr[slice_i][elem_i].lt)
            };

            rv.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
              state.vrf[slice_i][inst.rb][elem_i],
              state.vrf[slice_i][inst.ra][elem_i],
              state.vcr[slice_i][elem_i],
              inst.cond);

            msg = {msg,
              $sformatf(" %h\n",
                state.vrf[slice_i][inst.rt][elem_i])
            };
          end
        end
      endcase
    end

    //rv.print_vector(inst.rt);

    state = rv;
  endfunction


  function bit predict_byte(Vector_instruction inst,
      My_vector_state state,
      Sit::State pu_state);
    My_vector_state::Vector_double_bytes u, v, y, a;
    bit save_reg;
    bit save_acc;

    save_reg = 0;
    save_acc = 0;

    for(int slice_i=0; slice_i<NUM_SLICES; slice_i++) begin
      for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
        {u[2*elem_i], u[2*elem_i+1]} = sign_extend(state.vrf[slice_i][inst.ra][elem_i], VALU_TYPE_HALF);
        {v[2*elem_i], v[2*elem_i+1]} = sign_extend(state.vrf[slice_i][inst.rb][elem_i], VALU_TYPE_HALF);
        {a[2*elem_i], a[2*elem_i+1]} = state.accumulator[slice_i][elem_i];
      end

      case(inst.xo)
        Xop_fxvmtacb: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = u[byte_i];
            msg = {msg, $sformatf("(slice=%2d, byte=%2d)  ACC <- %h\n",
              slice_i, byte_i, y[byte_i]
            )};
          end
          save_acc = 1;
        end

        Xop_fxvmabm: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = u[byte_i] * v[byte_i] + a[byte_i];
            msg = {msg, $sformatf("(slice=%2d, byte=%2d)  %h = %h * %h + %h\n",
              slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i], a[byte_i]
            )};
          end
          save_reg = 1;
        end

        Xop_fxvmatacbm: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = u[byte_i] * v[byte_i] + a[byte_i];
            msg = {msg, $sformatf("(slice=%2d, byte=%2d)  %h = %h * %h + %h\n",
              slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i], a[byte_i]
            )};
          end
          save_acc = 1;
        end

        Xop_fxvmulbm: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = u[byte_i] * v[byte_i];
            msg = {msg, $sformatf("(slice=%2d, byte=%2d)  %h = %h * %h\n",
              slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i]
            )};
          end
          save_reg = 1;
        end

        Xop_fxvmultacbm: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = u[byte_i] * v[byte_i];
            msg = {msg, $sformatf("(slice=%2d, byte=%2d)  %h = %h * %h\n",
              slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i]
            )};
          end
          save_acc = 1;
        end

        Xop_fxvsubbm: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = u[byte_i] - v[byte_i];
            msg = {msg, $sformatf("(slice=%2d, byte=%2d)  %h = %h - %h\n",
              slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i]
            )};
          end
          save_reg = 1;
        end

        Xop_fxvaddactacb: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = u[byte_i] + a[byte_i];
            msg = {msg, $sformatf("(slice=%2d, byte=%2d)  %h = %h + %h\n",
              slice_i, byte_i, y[byte_i], u[byte_i], a[byte_i]
            )};
          end
          save_acc = 1;
        end

        Xop_fxvaddacbm: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = u[byte_i] + a[byte_i];
            msg = {msg, $sformatf("(slice=%2d, byte=%2d)  %h = %h + %h\n",
              slice_i, byte_i, y[byte_i], u[byte_i], a[byte_i]
            )};
          end
          save_reg = 1;
        end

        Xop_fxvaddtacb: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = u[byte_i] + v[byte_i];
            msg = {msg, $sformatf("(slice=%2d, byte=%2d)  %h = %h + %h\n",
              slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i]
            )};
          end
          save_acc = 1;
        end

        Xop_fxvaddbm: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = u[byte_i] + v[byte_i];
            msg = {msg, $sformatf("(slice=%2d, byte=%2d)  %h = %h + %h\n",
              slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i]
            )};
          end
          save_reg = 1;
        end

        Xop_fxvcmpb: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i += 2) begin
            int x0, x1;

            x0 = signed'(u[byte_i]);
            x1 = signed'(u[byte_i+1]);

            state.vcr[slice_i][byte_i/2].eq = {
              {$bits(state.vcr[slice_i][byte_i/2].eq)/2{ (x0 == 0) }},
              {$bits(state.vcr[slice_i][byte_i/2].eq)/2{ (x1 == 0) }}
            };
            state.vcr[slice_i][byte_i/2].lt = {
              {$bits(state.vcr[slice_i][byte_i/2].lt)/2{ (x0 < 0) }},
              {$bits(state.vcr[slice_i][byte_i/2].lt)/2{ (x1 < 0) }}
            };
            state.vcr[slice_i][byte_i/2].gt = {
              {$bits(state.vcr[slice_i][byte_i/2].gt)/2{ (x0 > 0) }},
              {$bits(state.vcr[slice_i][byte_i/2].gt)/2{ (x1 > 0) }}
            };

            msg = {msg, $sformatf("(slice_i=%2d, elem_i=%2d)  VCR.eq = %h, VCR.lt = %h, VCR.gt = %h",
                slice_i, byte_i/2, state.vcr[slice_i][byte_i/2].eq,
                state.vcr[slice_i][byte_i/2].lt, state.vcr[slice_i][byte_i/2].lt)};
            msg = {msg, $sformatf("  x0 = %h, x1 = %h\n",
                x0, x1)};
          end
        end

        Xop_fxvsplatb: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            My_vector_state::Vector_half_element splt;

            splt = pu_state.get_gpr(inst.ra);

            state.vrf[slice_i][inst.rt][elem_i] = { splt, splt };

            msg = {msg, $sformatf("(slice_i=%2d, elem_i=%2d)  VRF[%2d] <- %h\n",
                slice_i, elem_i, inst.rt, splt)};
          end
        end

        Xop_fxvshb: begin
          for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
            logic signed[4:0] shift_amount;

            shift_amount = inst.rb;

            msg = {msg,
              $sformatf("shift_amount = %2d, %h ->",
                shift_amount,
                state.vrf[slice_i][inst.ra][elem_i])
            };

            if( shift_amount < 0)
              state.vrf[slice_i][inst.rt][elem_i] = {
                state.vrf[slice_i][inst.ra][elem_i][ELEM_SIZE-1 -: ELEM_SIZE/2] >> -shift_amount,
                state.vrf[slice_i][inst.ra][elem_i][ELEM_SIZE/2-1 -: ELEM_SIZE/2] >> -shift_amount
              };
            else
              state.vrf[slice_i][inst.rt][elem_i] = {
                state.vrf[slice_i][inst.ra][elem_i][ELEM_SIZE-1 -: ELEM_SIZE/2] << shift_amount,
                state.vrf[slice_i][inst.ra][elem_i][ELEM_SIZE/2-1 -: ELEM_SIZE/2] << shift_amount
              };

            msg = {msg,
              $sformatf(" %h\n",
                state.vrf[slice_i][inst.rt][elem_i])
            };
          end
        end

        default: return 0;
      endcase

      for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
        My_vector_state::Vector_double_element yy;

        if( save_reg || save_acc ) begin
          yy = {y[2*elem_i], y[2*elem_i+1]};
          msg = {msg, $sformatf("(slice=%2d, elem_i=%2d)  yy = %h (VRF=%h)  VCR = (eq=%4b, lt=%4b, gt=%4b) cond=%s\n",
              slice_i, elem_i, yy,
              state.vrf[slice_i][inst.rt][elem_i],
              state.vcr[slice_i][elem_i].eq,
              state.vcr[slice_i][elem_i].lt,
              state.vcr[slice_i][elem_i].gt,
              inst.cond)};
        end

        if( save_reg ) begin
          state.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
            modulo_extract(yy, VALU_TYPE_HALF),
            state.vrf[slice_i][inst.rt][elem_i],
            state.vcr[slice_i][elem_i],
            inst.cond
          );
        end

        if( save_acc ) begin
          state.accumulator[slice_i][elem_i] = mask_conditional_double(yy,
            state.accumulator[slice_i][elem_i],
            state.vcr[slice_i][elem_i],
            inst.cond);
        end
      end
    end

    return 1;
  endfunction


  function bit predict_byte_fractional(Vector_instruction inst,
      My_vector_state state,
      Sit::State pu_state);
    shortint u[My_vector_state::BYTES_PER_VECTOR];
    shortint v[My_vector_state::BYTES_PER_VECTOR];
    shortint y[My_vector_state::BYTES_PER_VECTOR];
    shortint a[My_vector_state::BYTES_PER_VECTOR];
    bit save_reg;
    bit save_acc;
    bit shift_left;

    save_reg = 0;
    save_acc = 0;
    shift_left = 1;

    for(int slice_i=0; slice_i<NUM_SLICES; slice_i++) begin
      for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
        {u[2*elem_i], u[2*elem_i+1]} = signed'(sign_extend(state.vrf[slice_i][inst.ra][elem_i], VALU_TYPE_HALF));
        {v[2*elem_i], v[2*elem_i+1]} = signed'(sign_extend(state.vrf[slice_i][inst.rb][elem_i], VALU_TYPE_HALF));
        {a[2*elem_i], a[2*elem_i+1]} = signed'(state.accumulator[slice_i][elem_i]);
      end

      case(inst.xo)
        Xop_fxvmabfs: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = mult_add_sat_fract(u[byte_i], v[byte_i], a[byte_i], ELEM_SIZE/2);

            msg = {msg, $sformatf("(slice_i=%2d, byte_i=%2d)  %h = %h * %h + %h\n",
                slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i], a[byte_i])};
          end

          save_reg = 1;
        end

        Xop_fxvmatacbfs: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = mult_add_sat_fract(u[byte_i], v[byte_i], a[byte_i], ELEM_SIZE/2);

            msg = {msg, $sformatf("(slice_i=%2d, byte_i=%2d)  %h = %h * %h + %h\n",
                slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i], a[byte_i])};
          end

          save_acc = 1;
        end

        Xop_fxvmulbfs: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = mult_sat_fract(u[byte_i], v[byte_i], ELEM_SIZE/2);

            msg = {msg, $sformatf("(slice_i=%2d, byte_i=%2d)  %h = %h * %h\n",
                slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i])};
          end

          save_reg = 1;
        end

        Xop_fxvmultacbfs: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = mult_sat_fract(u[byte_i], v[byte_i], ELEM_SIZE/2);

            msg = {msg, $sformatf("(slice_i=%2d, byte_i=%2d)  %h = %h * %h\n",
                slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i])};
          end

          save_acc = 1;
        end

        Xop_fxvsubbfs: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = add_sat(u[byte_i], -v[byte_i], ELEM_SIZE/2) << ELEM_SIZE/2;

            msg = {msg, $sformatf("(slice_i=%2d, byte_i=%2d)  %h = %h - %h\n",
                slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i])};
          end

          shift_left = 0;
          save_reg = 1;
        end

        Xop_fxvaddactacbf: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = add_sat(u[byte_i] << ELEM_SIZE/2, a[byte_i], ELEM_SIZE);

            msg = {msg, $sformatf("(slice_i=%2d, byte_i=%2d)  %h = %h + %h\n",
                slice_i, byte_i, y[byte_i], u[byte_i], a[byte_i])};
          end

          save_acc = 1;
        end

        Xop_fxvaddacbfs: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = add_sat(u[byte_i] << ELEM_SIZE/2, a[byte_i], ELEM_SIZE);

            msg = {msg, $sformatf("(slice_i=%2d, byte_i=%2d)  %h = %h + %h\n",
                slice_i, byte_i, y[byte_i], u[byte_i], a[byte_i])};
          end

          shift_left = 0;
          save_reg = 1;
        end

        Xop_fxvaddbfs: begin
          for(int byte_i=0; byte_i<2*NUM_ELEMS; byte_i++) begin
            y[byte_i] = add_sat(u[byte_i], v[byte_i], ELEM_SIZE/2) << ELEM_SIZE/2;

            msg = {msg, $sformatf("(slice_i=%2d, byte_i=%2d)  %h = %h + %h\n",
                slice_i, byte_i, y[byte_i], u[byte_i], v[byte_i])};
          end

          shift_left = 0;
          save_reg = 1;
        end

        Xop_fxvmtacbf: begin
          for(int elem_i=0; elem_i<2*NUM_ELEMS; elem_i++) begin
            y[2*elem_i] = {
              state.vrf[slice_i][inst.ra][elem_i][ELEM_SIZE  -1 -: ELEM_SIZE/2], {ELEM_SIZE/2{1'b0}}
            };

            y[2*elem_i+1] = {
              state.vrf[slice_i][inst.ra][elem_i][ELEM_SIZE/2-1 -: ELEM_SIZE/2], {ELEM_SIZE/2{1'b0}}
            };

            msg = {msg, $sformatf("(slice_i=%2d, elem_i=%2d)  ACC <- %h  %h\n",
              slice_i, elem_i, y[2*elem_i], y[2*elem_i+1])};
          end

          save_acc = 1;
        end

        default: return 0;
      endcase

      for(int elem_i=0; elem_i<NUM_ELEMS; elem_i++) begin
        My_vector_state::Vector_double_element yy;

        if( save_reg || save_acc ) begin
          yy = {y[2*elem_i], y[2*elem_i+1]};
          msg = {msg, $sformatf("(slice=%2d, elem_i=%2d)  yy = %h (VRF=%h)  VCR = (eq=%4b, lt=%4b, gt=%4b) cond=%s\n",
              slice_i, elem_i, yy,
              state.vrf[slice_i][inst.rt][elem_i],
              state.vcr[slice_i][elem_i].eq,
              state.vcr[slice_i][elem_i].lt,
              state.vcr[slice_i][elem_i].gt,
              inst.cond)};
        end

        if( save_reg ) begin
          state.vrf[slice_i][inst.rt][elem_i] = mask_conditional(
            saturating_fractional_extract(yy, shift_left, VALU_TYPE_HALF),
            state.vrf[slice_i][inst.rt][elem_i],
            state.vcr[slice_i][elem_i],
            inst.cond
          );
        end

        if( save_acc ) begin
          state.accumulator[slice_i][elem_i] = mask_conditional_double(yy,
            state.accumulator[slice_i][elem_i],
            state.vcr[slice_i][elem_i],
            inst.cond);
        end
      end
    end

    return 1;
  endfunction


  function void clear_msg();
    msg = "";
  endfunction


  function My_vector_state::Vector_element modulo_extract(My_vector_state::Vector_double_element x,
      Valu_type conf);
    My_vector_state::Vector_element rv;

    unique case(conf)
      VALU_TYPE_FULL: rv = x[ELEM_SIZE-1:0];
      VALU_TYPE_HALF: rv = {
        x[ELEM_SIZE+(ELEM_SIZE/2)-1 -: ELEM_SIZE/2],
        x[ELEM_SIZE/2-1 -: ELEM_SIZE/2]
      };
      VALU_TYPE_QUARTER: rv = {
        x[ELEM_SIZE+(ELEM_SIZE/2)+(ELEM_SIZE/4)-1 -: ELEM_SIZE/4],
        x[ELEM_SIZE+(ELEM_SIZE/2)-(ELEM_SIZE/4)-1 -: ELEM_SIZE/4],
        x[          (ELEM_SIZE/2)+(ELEM_SIZE/4)-1 -: ELEM_SIZE/4],
        x[          (ELEM_SIZE/2)-(ELEM_SIZE/4)-1 -: ELEM_SIZE/4]
      };
      default: begin
        rv = 'x;
      end
    endcase

    return rv;
  endfunction


  function My_vector_state::Vector_double_element shift_left_saturating(My_vector_state::Vector_double_element x,
      Valu_type conf);
    My_vector_state::Vector_double_element rv;

    unique case(conf)
      VALU_TYPE_FULL:  begin
        if( (x[$left(x) -: 2] == 2'b01) )
          rv = { 1'b0, {2*ELEM_SIZE-1{1'b1}} };
        else
          rv = { x[$left(x)-1:$right(x)], 1'b0 };
      end

      // TODO other configurations

      default: rv = 'x;
    endcase

    return rv;
  endfunction


  function My_vector_state::Vector_element saturating_fractional_extract(My_vector_state::Vector_double_element x,
      bit shift_left,
      Valu_type conf);
    My_vector_state::Vector_element rv;
    logic sign_bit;
    logic guard_bit;

    unique case(conf)
      VALU_TYPE_FULL: begin
        rv = x[2*ELEM_SIZE-1:ELEM_SIZE];
      end

      VALU_TYPE_HALF: begin
        rv[ELEM_SIZE-1   : ELEM_SIZE/2] = x[2*ELEM_SIZE-1 -: ELEM_SIZE/2];
        rv[ELEM_SIZE/2-1 : 0          ] = x[ELEM_SIZE-1   -: ELEM_SIZE/2];
      end

      default: begin
        rv = 'x;
      end
    endcase

    return rv;
  endfunction


  /* Do sign extension depending on the vector configuration */
  function My_vector_state::Vector_double_element sign_extend(My_vector_state::Vector_element x, Valu_type conf);
    My_vector_state::Vector_double_element rv;
    My_vector_state::Vector_element_halfs halfs;
    My_vector_state::Vector_element_quarters quarters;

    halfs = My_vector_state::Vector_element_halfs'(x);
    quarters = My_vector_state::Vector_element_quarters'(x);

    unique case(conf)
      VALU_TYPE_FULL: rv = { {ELEM_SIZE{x[$left(x)]}}, x };
      VALU_TYPE_HALF: rv = {
        {ELEM_SIZE/2{halfs[0][ELEM_SIZE/2-1]}},
        halfs[0],
        {ELEM_SIZE/2{halfs[1][ELEM_SIZE/2-1]}},
        halfs[1]
      };
      VALU_TYPE_QUARTER: rv = {
        {ELEM_SIZE/4{quarters[0][ELEM_SIZE/4-1]}},
        quarters[0],
        {ELEM_SIZE/4{quarters[1][ELEM_SIZE/4-1]}},
        quarters[1],
        {ELEM_SIZE/4{quarters[2][ELEM_SIZE/4-1]}},
        quarters[2],
        {ELEM_SIZE/4{quarters[3][ELEM_SIZE/4-1]}},
        quarters[3]
      };
      default: rv = 'x;
    endcase

    return rv;
  endfunction


  function My_vector_state::Vector_element mask_conditional(
      input My_vector_state::Vector_element result, original,
      input Vector::Compare cmp,
      input Pu_inst::Fxv_cond cond);
    My_vector_state::Vector_element rv;
    logic[0:3] c;

    if( cond == Pu_inst::Fxv_cond_null )
      return result;

    case(cond)
      Pu_inst::Fxv_cond_gt: c = cmp.gt;
      Pu_inst::Fxv_cond_lt: c = cmp.lt;
      Pu_inst::Fxv_cond_eq: c = cmp.eq;
    endcase

    rv = {
      c[0] ? result[ELEM_SIZE-1 -: ELEM_SIZE/4] : original[ELEM_SIZE-1 -: ELEM_SIZE/4],
      c[1] ? result[(3*ELEM_SIZE/4)-1 -: ELEM_SIZE/4] : original[(3*ELEM_SIZE/4)-1 -: ELEM_SIZE/4],
      c[2] ? result[(ELEM_SIZE/2)-1 -: ELEM_SIZE/4] : original[(ELEM_SIZE/2)-1 -: ELEM_SIZE/4],
      c[3] ? result[(ELEM_SIZE/4)-1 -: ELEM_SIZE/4] : original[(ELEM_SIZE/4)-1 -: ELEM_SIZE/4]
    };

    return rv;
  endfunction


  function My_vector_state::Vector_double_element mask_conditional_double(
      input My_vector_state::Vector_double_element result, original,
      input Vector::Compare cmp,
      input Pu_inst::Fxv_cond cond);
    My_vector_state::Vector_double_element rv;
    logic[0:3] c;

    if( cond == Pu_inst::Fxv_cond_null )
      return result;

    case(cond)
      Pu_inst::Fxv_cond_gt: c = cmp.gt;
      Pu_inst::Fxv_cond_lt: c = cmp.lt;
      Pu_inst::Fxv_cond_eq: c = cmp.eq;
    endcase

    rv = {
      c[0] ? result[2*ELEM_SIZE-1 -: ELEM_SIZE/2] : original[2*ELEM_SIZE-1 -: ELEM_SIZE/2],
      c[1] ? result[(3*ELEM_SIZE/2)-1 -: ELEM_SIZE/2] : original[(3*ELEM_SIZE/2)-1 -: ELEM_SIZE/2],
      c[2] ? result[ELEM_SIZE-1 -: ELEM_SIZE/2] : original[ELEM_SIZE-1 -: ELEM_SIZE/2],
      c[3] ? result[(ELEM_SIZE/2)-1 -: ELEM_SIZE/2] : original[(ELEM_SIZE/2)-1 -: ELEM_SIZE/2]
    };

    return rv;
  endfunction


  function My_vector_state::Vector_bytes vector_to_bytes(input My_vector_state::Vector v);
    My_vector_state::Vector_bytes rv;

    //$display("start");
    for(int i=0; i<NUM_ELEMS; i++) begin
      My_vector_state::Vector_element_halfs u;

      u = v[i];
      rv[2*i] = u[0];
      rv[2*i+1] = u[1];

      //$display("vector_to_bytes: i=%d, u=%h, v[i]=%h, rv[2*i]=%h, rv[2*i+1]=%h",
        //i, u, v[i], rv[2*i], rv[2*i+1]);
    end
    //$display("stop");

    return rv;
  endfunction


  function My_vector_state::Vector bytes_to_vector(input My_vector_state::Vector_bytes v);
    My_vector_state::Vector rv;

    //$display("start");
    for(int i=0; i<NUM_ELEMS; i++) begin
      My_vector_state::Vector_element_halfs u;

      u[0] = v[2*i];
      u[1] = v[2*i+1];
      rv[i] = u;

      //$display("bytes_to_vector: i=%2d, u[0]=%h, u[1]=%h, v[2*i]=%h, v[2*i+1]=%h, rv[i]=%h",
        //i, u[0], u[1], v[2*i], v[2*i+1], rv[i]);
    end
    //$display("stop");

    return rv;
  endfunction

endclass

`endif

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
