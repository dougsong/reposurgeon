#!/bin/bash

# Takes two arguments, a type name and a file name. The file name
# specifies which data file to read from, and the type name specifies
# which type of graph to create. Each graph type comes from a gnuplot
# file, where the details of things like axes titles and such are
# kept.
#
# The gnuplot file also does both a linear and a quadratic fit to the
# data. Gnuplot prints the details of that fit to stderr. I haven't
# gotten to the point of capturing that data and making use of it yet.

type="${1}"
file="${2}"
gnuplot --persist -e "file='${file}'" "bench/bench-${type}.gnuplot" -
