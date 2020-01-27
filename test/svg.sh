#!/bin/bash

type="${1}"
datfile="${2}"
output="${3}"
gnuplot --persist -e "file='${datfile}'; set terminal svg size 1920,1080 dynamic name '${type}'" "bench-${type}.gnuplot" > "${output}"
