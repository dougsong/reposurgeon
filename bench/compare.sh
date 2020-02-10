#!/bin/bash

type="${1}"
output="${2}"
shift; shift
files="$@"
gnuplot --persist -e "files='${files}'; set terminal svg size 1920,1080 dynamic name '${type}'" "bench/compare-${type}.gnuplot" > "${output}"
