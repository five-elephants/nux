// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


package arithmetic;

  /**
   * Signed saturating addition with variable bit width (<=64).
   */
  function automatic longint add_sat(longint a, longint b, int num_bits);
    longint rv;

    assert( (num_bits > 0) && (num_bits <= 64) );

    if( a + b > 2 ** (num_bits-1) - 1 )
      rv = 2 ** (num_bits-1) - 1;
    else if( a + b < -2 ** (num_bits-1) )
      rv = -2 ** (num_bits-1);
    else
      rv = a + b;
    
    return rv;
  endfunction


  /**
   * Signed saturating multiplication with variable bit width (<=64)
   */
  function automatic longint mult_sat_fract(longint a, longint b, int num_bits);
    longint rv;

    assert( (num_bits > 0) && (2*num_bits <= 64) );

    if( (a == -2 ** (num_bits-1)) && (b == -2 ** (num_bits-1)) )
      rv = 2 ** (2*num_bits-1) - 1;
    else begin
      rv = a * b;
      rv = rv << 1;
    end

    return rv;
  endfunction


  /**
   * Signed, fractional, saturating multiply-add operation (num_bits <=
   * 32). c is a double sized operand.
   */
  function automatic longint mult_add_sat_fract(longint a, longint b, longint c, int num_bits);
    longint rv;
    longint prod;

    assert( (num_bits > 0) && (2*num_bits <= 64) );

    prod = mult_sat_fract(a, b, num_bits);
    rv = add_sat(prod, c, 2*num_bits); 

    return rv;
  endfunction


endpackage
