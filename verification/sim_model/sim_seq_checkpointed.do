transcript file "sequence_test.transcript"

do waves/sequence_test_wave.do
dataset snapshot -enable -file sequence_test.wlf -time {5 ms}

for {set i 0} {$i < 20} {incr i} {
	puts "Iteration $i ..."

	run 5 ms

	puts "Assertion fail count: [assertion count -fails -recursive /]"
	assertion report -recursive -file assertion_report.txt /
	checkpoint "after-$i.checkpoint"
}

dataset save sim sequence_test.wlf
exit

