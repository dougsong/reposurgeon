#!/bin/bash
set -x

function run {
    datfile="${1}"
    logfile="${2}"
    dump="${3}"
    readlimit="${4}"
    /usr/bin/time -f "${readlimit} %e %M %K" -a -o "${datfile}" \
                  ./reposurgeon "logfile ${logfile}" \
                                "readlimit ${readlimit}" \
                                "read <${dump}" 2>&- 1>&-
}

dump="${1}"
min="${2}"
step="${3}"
max="${4}"
rev="$(git rev-parse HEAD)"
for readlimit in $(seq "${min}" "${step}" "${max}"); do
    run "${rev}.dat" "${rev}-${readlimit}.log" "${dump}" "${readlimit}"
done

./plot.sh runtime "${file}"
