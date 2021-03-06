#!/bin/sh
## Test standard CVS to Git workflow

# This is how we detect we're in Gitlab CI.
if [ -z "${USER}" ]
then
    echo "SKIPPED - ssh is blocked in CI, so rsync will fail"
    exit 0
fi

command -v cvs >/dev/null 2>&1 || { echo "    Skipped, cvs missing."; exit 0; }
command -v cvs-fast-export >/dev/null 2>&1 || { echo "    Skipped, cvs-fast-export missing."; exit 0; }

set -e

TMPDIR=${TMPDIR:-/tmp}

trap 'rm -rf ${TMPDIR}/cvs-scratch$$ ${TMPDIR}/ref$$ ${TMPDIR}/out$$' EXIT HUP INT QUIT TERM

# Go to our sandbox
here=$(realpath .)
mkdir "${TMPDIR}/cvs-scratch$$"
cd "${TMPDIR}/cvs-scratch$$" >/dev/null || (echo "$0: cd failed" >&2; exit 1)

# Make the workflow file.
repotool initialize -q hack1 cvs git

# Convert the repository
make --silent -e REMOTE_URL="cvs://localhost${here}/hack1.repo#module" VERBOSITY="" 2>&1 | sed "/ no commitids before/"d

# Compare the results
repotool compare-all hack1-mirror hack1-git || echo "FAILED: Repositories do not compare equal."

# No output is good news

#end
