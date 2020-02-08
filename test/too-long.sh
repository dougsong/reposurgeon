#!/bin/bash

# I used this script to bisect a performance regression using git
# bisect run. I knew that with a readlimit of 10k, the good revision
# took less than 10 seconds to complete, while the bad revision took
# 30 seconds. Adjust to suit your situation.

make 1>&- 2>&-
t=$(/usr/bin/time -f "%e" ./reposurgeon "logfile /dev/null" "readlimit 10000" "read <gcc.svn" 2>&1 | cut -d . -f 1)
echo "time was ${t}s"
[[ t -lt 20 ]]
