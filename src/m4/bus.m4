divert(-1)

dnl define(`LQ', `changequote(<,>)`dnl'
dnl changequote`'')
dnl define(`RQ', `changequote(<,>)dnl`
dnl 'changequote`'')

changequote(<:,:>)

define(<:bus_begin:>, <:
// begin bus $1 dnl
pushdef(<:busprefix:>, <:$1:>)dnl
define(<:busclk:>, <:$2:>)dnl
define(<:out_n:>, <:-1:>)dnl
define(<:node_n:>, <:-1:>)dnl
define(<:interfaceparam:>, ifelse($3, <::>, <::>, <: <:<:#:>($3):>:>))dnl
:>)

define(<:bus_end:>, <:// end bus busprefix popdef(<:busprefix:>):>)

define(<:master:>, <:pushdef(<:busout:>, <:$1:>):>)
define(<:slave:>, <:define(busprefix()_slave_$1, busout)popdef(<:busout:>):>)

dnl define(<:with_byteen:>. <:.byteen(1):>)
define(<:num_in_flight:>, <:.NUM_IN_FLIGHT($1):>)

define(<:arb:>, <:
define(<:node_n:>, incr(node_n))dnl
Bus_if<::>interfaceparam() busprefix()_out_<::>incr(out_n) (.Clk(busclk));
Bus_if_arb ifelse($1,<::>, <::>, <:<:#:>($1):>) busprefix()_a<::>node_n() (
  .in_1(busout)popdef(<:busout:>),
  .in_0(busout)popdef(<:busout:>),
define(<:out_n:>, incr(out_n))dnl
pushdef(<:busout:>, <:busprefix()_out_<::>out_n():>)dnl
  .out(busout)
);
:>)

define(<:delay:>, <:
define(<:node_n:>, incr(node_n))dnl
Bus_if<::>interfaceparam() busprefix()_out_<::>incr(out_n) (.Clk(busclk));
Bus_delay busprefix()_d<::>node_n() (
  .in(busout)popdef(<:busout:>),
define(<:out_n:>, incr(out_n))dnl
pushdef(<:busout:>, <:busprefix()_out_<::>out_n():>)dnl
  .out(busout)
);
:>)

define(<:split:>, <:
define(<:node_n:>, incr(node_n))dnl
Bus_if<::>interfaceparam() busprefix()_out_<::>incr(out_n) (.Clk(busclk));
Bus_if<::>interfaceparam() busprefix()_out_<::>incr(incr(out_n)) (.Clk(busclk));
Bus_if_split <:#:>($1 $2) busprefix()_d<::>node_n() (
  .top(busout)popdef(<:busout:>),
define(<:out_n:>, incr(out_n))dnl
pushdef(<:busout:>, busprefix()_out_<::>out_n())dnl
  .out_1(busout),
define(<:out_n:>, incr(out_n))dnl
pushdef(<:busout:>, busprefix()_out_<::>out_n())dnl
  .out_0(busout)
);
:>)

divert(0)dnl
dnl
dnl bus_begin(test, clk)
dnl   master(one)
dnl   master(two) arb
dnl     master(three) arb(num_in_flight(16))
dnl       delay
dnl       split(31, num_in_flight(8)) slave(a)
dnl         split(30) slave(b) slave(c)
dnl bus_end()
dnl 
dnl my_module(
dnl   .slave_a(test_slave_a),
dnl   .slave_b(test_slave_b),
dnl   .slave_c(test_slave_c)
dnl );
dnl 
