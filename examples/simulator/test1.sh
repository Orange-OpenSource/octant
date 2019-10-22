#!/bin/bash

python3 test1.py -o backup.csv
rm -f perf1.dat

for i in $(seq 8 12); do
    t1=$(octant --config-file conf.cfg --doc --theory test.dtl --restore backup.csv --query "result(X)" --ipsize "$i" --time | grep 'Query time:' | sed 's/.*: //')
    t2=$(octant --config-file conf.cfg --nodoc --theory test.dtl --restore backup.csv --query "result(X)" --ipsize "$i" --time | grep 'Query time:' | sed 's/.*: //')
    echo "$i,$t1,$t2" >> perf1.dat
done

for i in $(seq 13 63); do
  for j in $(seq 1 10); do
    t1=$(octant --config-file conf.cfg --doc --theory test.dtl --restore backup.csv --query "result(X)" --ipsize "$i" --time | grep 'Query time:' | sed 's/.*: //')
    echo "$i,$t1,-" >> perf1.dat
  done
done
