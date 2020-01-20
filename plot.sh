#!/bin/bash

type="${1}"
file="${2}"
gnuplot --persist -e "file='${file}'" "bench-${type}.gnuplot" -
