#!/bin/bash

file="${1}"
gnuplot --persist -e "file='${file}'" bench.gnuplot
