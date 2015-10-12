// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Result_if;
  import Backend::*;

  Result_bus res_0;
  Result_bus res_1;
  Result_bus res_2;
  Result_bus res_3;
  Result_bus res_4;
  Result_bus res_5;
  Result_bus res_6;
  Result_bus res_7;

  function automatic Result_bus get_res(input logic[2:0] sel);
    //unique case(sel)
      //0: return res_0;
      //1: return res_1;
      //2: return res_2;
      //3: return res_3;
      //4: return res_4;
      //default: return result_bus_undef();
    //endcase
    unique case(sel)
      0: get_res = res_0;
      1: get_res = res_1;
      2: get_res = res_2;
      3: get_res = res_3;
      4: get_res = res_4;
      5: get_res = res_5;
      6: get_res = res_6;
      7: get_res = res_7;
      default: get_res = result_bus_undef();
    endcase
  endfunction

  function automatic void set_res(input logic[2:0] sel, Result_bus b);
    unique case(sel)
      0: res_0 = b;
      1: res_1 = b;
      2: res_2 = b;
      3: res_3 = b;
      4: res_4 = b;
      5: res_5 = b;
      6: res_6 = b;
      7: res_7 = b;
      default: begin
        res_0 = result_bus_undef();
        res_1 = result_bus_undef();
        res_2 = result_bus_undef();
        res_3 = result_bus_undef();
        res_4 = result_bus_undef();
        res_5 = result_bus_undef();
        res_6 = result_bus_undef();
        res_7 = result_bus_undef();
      end
    endcase
  endfunction


  //Result_bus res;
  //Result_bus res[0:4];
  //Result_bus_array res;

  //function automatic Result_bus get_res(input Frontend::Fu_set_id sel);
    //return res[sel];
  //endfunction

  //function automatic Result_bus_array get_res();
    ////return res;
  //endfunction

  //function automatic logic get_res();
    //return 1'b0;
  //endfunction

  //function automatic void set_res(input Result_bus_array ar);
    ////res = ar;
  //endfunction

  //modport write_back(input res);
  //modport fub(output res);
  modport write_back(import get_res, input res_0, res_1, res_2, res_3, res_4, res_5, res_6, res_7);
  modport fub(import set_res, output res_0, res_1, res_2, res_3, res_4, res_5, res_6, res_7);
endinterface


// vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
