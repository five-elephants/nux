// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


module Signoff_vector_test();

  Fub_vector_test #(
    .DO_INST_SEQUENCE_TEST(1'b1),
    .SINGLE_TEST_SIZE(20000),
    //.SINGLE_TEST_SIZE(0),
    .BULK_TEST_SIZE(20000),
    .BULK_SIZE(32)
    //.BULK_SIZE(4)
  ) test ();

endmodule

/* vim: set et fenc= ff=unix sts=0 sw=2 ts=2 : */
