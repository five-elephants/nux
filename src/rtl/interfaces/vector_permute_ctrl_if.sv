// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


interface Vector_permute_ctrl_if();
  Vector::Permute_op op;

  logic pack_upper;
  logic pack_lower;
  logic unpack_left;
  logic unpack_right;

  Pu_types::Word g;

  Vector::Permute_size size;

  logic[4:0] shift;

  logic keep_res;


  modport ctrl(
    output op, pack_upper, pack_lower, unpack_left, unpack_right, g,
    size, shift, keep_res
  );

  modport permute(
    input op, pack_upper, pack_lower, unpack_left, unpack_right, g, size,
    shift, keep_res
  );

endinterface

