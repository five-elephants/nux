
//---------------------------------------------------------------------------
/** ncsim does not allow to have an unpacked array or struct expression in
* a port connection statement. These macros create an additional signal that
* is then connected to the port. */
`define ARRAY_EXTRACT_IN(typ, arr, indx) \
typ arr``__``indx;\
assign arr``__``indx = arr[indx];

`define ARRAY_EXTRACT_OUT(typ, arr, indx) \
typ arr``__``indx;\
assign arr[indx] = arr``__``indx;

`define FROM_ARRAY(arr, indx) \
arr``__``indx
//---------------------------------------------------------------------------

