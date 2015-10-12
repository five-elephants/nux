// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Valu_test();
  localparam time clk_period = 10ns;
  localparam int NUM_ELEMS = 8;
  localparam int ELEM_SIZE = 16;
  localparam int SCALAR_SIZE = 32;
  localparam int MULT_STAGES = 1;
  localparam int ADD_STAGES = 1;
  localparam int DELAY = MULT_STAGES + ADD_STAGES;

  typedef logic[ELEM_SIZE-1:0] Vector_element;
  typedef Vector_element Vector_elems[0:NUM_ELEMS-1];
  typedef bit signed[ELEM_SIZE*2-1:0] Vector_double_element_signed;
  typedef bit signed[ELEM_SIZE-1:0] Vector_element_signed;
  typedef bit signed[ELEM_SIZE/2-1:0] Vector_half_element_signed;
  typedef bit signed[ELEM_SIZE/4-1:0] Vector_quarter_element_signed;
  
  logic clk, reset;

  logic valid;
  Valu_pkg::Valu_operation op;
  logic elem_en[0:NUM_ELEMS-1];
  logic[NUM_ELEMS*ELEM_SIZE-1:0] a;
  logic[NUM_ELEMS*ELEM_SIZE-1:0] b;
  logic[NUM_ELEMS*ELEM_SIZE-1:0] c;
  logic[SCALAR_SIZE-1:0] g;
  logic[NUM_ELEMS*ELEM_SIZE-1:0] y;

  Valu_ctrl_if #(
    .MULT_STAGES(MULT_STAGES),
    .ADD_STAGES(ADD_STAGES)
  ) valu_ctrl_if();

  Valu_ctrl #(
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .SCALAR_SIZE(SCALAR_SIZE),
    .MULT_STAGES(MULT_STAGES),
    .ADD_STAGES(ADD_STAGES)
  ) valu_ctrl_ut (
    .clk,
    .reset,
    .valid,
    .op,
    .ctrl(valu_ctrl_if.ctrl)
  );

  Valu #(
    .NUM_ELEMS(NUM_ELEMS),
    .ELEM_SIZE(ELEM_SIZE),
    .SCALAR_SIZE(SCALAR_SIZE),
    .MULT_STAGES(MULT_STAGES),
    .ADD_STAGES(ADD_STAGES)
  ) valu_ut (
    .clk,
    .reset,
    .elem_en,
    .ctrl(valu_ctrl_if.valu),
    .a,
    .b,
    .g,
    .y
  );


  always begin
    clk = 1'b0;
    #(clk_period/2);
    clk = 1'b1;
    #(clk_period/2);
  end

  //--------------------------------------------------------------------------------
  // Constraint random test class
  //--------------------------------------------------------------------------------
  
  class Valu_test_operation;
    typedef enum {
      MULT,
      ADD,
      MULT_ADD
    } Test_operation;
      
    rand Vector_element u[NUM_ELEMS];
    rand Vector_element v[NUM_ELEMS];
    rand Vector_element w[NUM_ELEMS];
    rand Valu_pkg::Valu_type op_type;
    rand Test_operation test_op;

    constraint force_operation {
      //test_op == MULT_ADD && op_type == Valu_pkg::VALU_TYPE_HALF;
      test_op == MULT_ADD;
    }

    task automatic test();
      test_operation();
    endtask


    //--------------------------------------------------------------------------------
    function automatic int compute_result(Test_operation op, Vector_element u, v, w);
      int rv;

      case(op)
        MULT:     rv = u * v;
        ADD:      rv = u + w;
        MULT_ADD: rv = u * v + w;
      endcase

      return rv;
    endfunction 
    //--------------------------------------------------------------------------------
    function automatic string op_to_name(Test_operation op);
      string rv;

      case(op)
        MULT: rv = "MULT";
        ADD: rv = "ADD";
        MULT_ADD: rv = "MULT_ADD";
      endcase

      return rv;
    endfunction
    //--------------------------------------------------------------------------------
    function automatic string type_to_string(Valu_pkg::Valu_type op_type);
      string rv;

      case(op_type)
        Valu_pkg::VALU_TYPE_FULL: rv = "full";
        Valu_pkg::VALU_TYPE_HALF: rv = "half";
        Valu_pkg::VALU_TYPE_QUARTER: rv = "quarter";
      endcase

      return rv;
    endfunction
    //--------------------------------------------------------------------------------
    task automatic test_operation();
      Vector_elems va;
      Vector_elems vb;
      Vector_elems vc;
      Vector_elems vy;
      Vector_elems exp_res;
      
      valid <= 1'b1;
      op.mult <= 1'b0;
      op.add <= 1'b0;
      op.scalar <= 1'b0;
      op.op_type <= op_type;

      case(test_op)
        MULT: op.mult <= 1'b1;
        ADD: op.add <= 1'b1;
        MULT_ADD: begin
          op.mult <= 1'b1;
          op.add <= 1'b1;
        end
      endcase

      for(int i=0; i<NUM_ELEMS; i++) begin
        int unsigned part_size;

        va[i] = u[i];
        vb[i] = v[i];
        vc[i] = w[i];

        case(op_type)
          Valu_pkg::VALU_TYPE_FULL: exp_res[i] = Vector_element_signed'(compute_result(test_op, u[i], v[i], w[i]));
          Valu_pkg::VALU_TYPE_HALF: exp_res[i] = { 
            Vector_half_element_signed'(compute_result(test_op,
                u[i][ELEM_SIZE-1 : ELEM_SIZE/2],
                v[i][ELEM_SIZE-1 : ELEM_SIZE/2], 
                w[i][ELEM_SIZE-1 : ELEM_SIZE/2])),
            Vector_half_element_signed'(compute_result(test_op,
                u[i][(ELEM_SIZE/2)-1 : 0],
                v[i][(ELEM_SIZE/2)-1 : 0],
                w[i][(ELEM_SIZE/2)-1 : 0]))
          };
          Valu_pkg::VALU_TYPE_QUARTER: exp_res[i] = {
            Vector_quarter_element_signed'(compute_result(test_op,
                u[i][ELEM_SIZE-1 : 3*ELEM_SIZE/4],
                v[i][ELEM_SIZE-1 : 3*ELEM_SIZE/4],
                w[i][ELEM_SIZE-1 : 3*ELEM_SIZE/4])),
            Vector_quarter_element_signed'(compute_result(test_op,
                u[i][3*ELEM_SIZE/4-1 : 2*ELEM_SIZE/4],
                v[i][3*ELEM_SIZE/4-1 : 2*ELEM_SIZE/4],
                w[i][3*ELEM_SIZE/4-1 : 2*ELEM_SIZE/4])),
            Vector_quarter_element_signed'(compute_result(test_op,
                u[i][2*ELEM_SIZE/4-1 : 1*ELEM_SIZE/4],
                v[i][2*ELEM_SIZE/4-1 : 1*ELEM_SIZE/4],
                w[i][2*ELEM_SIZE/4-1 : 1*ELEM_SIZE/4])),
            Vector_quarter_element_signed'(compute_result(test_op,
                u[i][1*ELEM_SIZE/4-1 : 0],
                v[i][1*ELEM_SIZE/4-1 : 0],
                w[i][1*ELEM_SIZE/4-1 : 0]))
          };
        endcase
      end

      for(int i=0; i<NUM_ELEMS; i++) begin
        a[(i+1)*ELEM_SIZE-1 -: ELEM_SIZE] <= va[i];
        b[(i+1)*ELEM_SIZE-1 -: ELEM_SIZE] <= vb[i];
        c[(i+1)*ELEM_SIZE-1 -: ELEM_SIZE] <= vc[i];
      end

      valid <= #(clk_period) 1'b0;
      for(int i=0; i<MULT_STAGES+ADD_STAGES; i++)
        @(posedge clk);
      @(negedge clk);

      //$display("checking");
      foreach(vy[i]) begin
        vy[i] = y[(i+1)*ELEM_SIZE-1 -: ELEM_SIZE];

        check_result: assert(vy[i] == exp_res[i]) else
          $error("test_op got unexpected result for operation '%s%s' in element %2d: 0x%h, should be 0x%h\n (u=0x%h, v=0x%h, w=0x%h)",
               op_to_name(test_op), type_to_string(op_type), i, vy[i], exp_res[i], u[i], v[i], w[i]); 
      end
    endtask
    //--------------------------------------------------------------------------------

  endclass


  //--------------------------------------------------------------------------------
  // Test program
  //--------------------------------------------------------------------------------

  initial begin
    Valu_test_operation vtest;

    vtest = new();

    reset = 1'b1;
    valid = 1'b0;
    {>>{elem_en}} = {NUM_ELEMS{1'b1}};
    #(10*clk_period) reset = 1'b0;

    @(posedge clk);

    //for(int n=0; n<100000; n++) begin
    //for(int n=0; n<100; n++) begin
    for(int n=0; n<8; n++) begin
      void'(vtest.randomize());

      //fork
        vtest.test();
      //join_none
      
      @(posedge clk);
    end

    wait fork;
    $stop;
  end
endmodule


/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
