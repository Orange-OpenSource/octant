#!/bin/bash

python3 test1.py -o backup.csv
rm -f perf2.dat

for i in $(seq 8 63); do
  mean=0.0
  max=0.0
  min=1000.0
  for j in $(seq 1 10); do
    t1=$(octant --config-file conf.cfg --doc --theory test.dtl --restore backup.csv --query "result(X)" --ipsize "$i" --time | grep 'Query time:' | sed 's/.*: //')
    mean=$(bc <<< "${mean} + ${t1}")
    if (( $(bc <<< "${t1} < ${min}") )); then min=$t1; fi
    if (( $(bc <<< "${t1} > ${max}") )); then max=$t1; fi
  done
  avg=$(echo "${mean} / 10.0" | bc -l)
  echo "$i,$avg,$min,$max" >> perf2.dat
done

gnuplot - <<EOF
set terminal png size 1000,1000; set output 'perf2.png'
plot [6:64] "perf2.dat" using 1:2:3:4 with yerrorlines lt -1 notitle
EOF
