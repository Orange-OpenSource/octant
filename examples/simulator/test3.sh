#!/bin/bash

rm -f perf3.dat
for i in $(seq 1 100); do
  mean=0.0
  max=0.0
  min=1000.0
  python3 test2.py $i -o backup.csv
  for j in $(seq 1 10); do
    t1=$(octant --config-file conf.cfg --doc --theory test.dtl --restore backup.csv --query "result(X)" --time | grep 'Query time:' | sed 's/.*: //')
    mean=$(bc <<< "${mean} + ${t1}")
    if (( $(bc <<< "${t1} < ${min}") )); then min=$t1; fi
    if (( $(bc <<< "${t1} > ${max}") )); then max=$t1; fi
  done
  avg=$(echo "${mean} / 10.0" | bc -l)
  echo "$i, $avg, $min, $max" >> perf3.dat
done

gnuplot - <<EOF
set terminal png size 1000,1000; set output 'perf3.png'
plot [6:64] "perf3.dat" using 1:2:3:4 with yerrorlines lt -1 notitle
EOF
