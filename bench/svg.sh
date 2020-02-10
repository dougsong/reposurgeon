#!/bin/bash

# Like plot.sh, but saves the graph to an svg file. The third argument
# is the filename to save to.
#
# You could use plot.sh to view the graph, and then use the viewer to
# save an svg file. However, that has some drawbacks; in particular
# the size of the graph will be fixed rather than dynamic.

type="${1}"
datfile="${2}"
output="${3}"
gnuplot --persist -e "file='${datfile}'; set terminal svg size 1920,1080 dynamic name '${type}'" "bench/bench-${type}.gnuplot" > "${output}"
