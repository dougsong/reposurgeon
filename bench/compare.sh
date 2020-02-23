#!/bin/bash

# Like svg.sh, but plots multiple data files. Currently this is
# over-specialized, because I use it to generate oops.svg. You'll
# likely want to customize it to your own requirements.
#
# You could use plot.sh to view the graph, and then use the viewer to
# save an svg file. However, that has some drawbacks; in particular
# the size of the graph will be fixed rather than dynamic, which means
# that it won't resize to your browser window.


type="${1}"
output="${2}"
shift; shift
files="$@"
gnuplot --persist -e "files='${files}'; set terminal svg size 1920,1080 dynamic name '${type}'" "bench/compare-${type}.gnuplot" > "${output}"
