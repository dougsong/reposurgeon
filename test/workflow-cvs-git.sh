#!/bin/sh
## Test standard CVS to Git workflow

command -v cvs >/dev/null 2>&1 || { echo "    Skipped, cvs missing."; exit 0; }
command -v cvs-fast-export >/dev/null 2>&1 || { echo "    Skipped, cvs-fast-export missing."; exit 0; }

set -e

TMPDIR=${TMPDIR:-/tmp}

trap 'rm -rf ${TMPDIR}/scratch$$ ${TMPDIR}/ref$$ ${TMPDIR}/out$$' EXIT HUP INT QUIT TERM

# Go to our sandbox
here=$(realpath .)
mkdir "${TMPDIR}/scratch$$"
cd "${TMPDIR}/scratch$$" >/dev/null || (echo "$0: cd failed" >&2; exit 1)

# Make the workflow file.
repotool initialize -q hack1 cvs git

# Convert the repository
make --silent -e REMOTE_URL="cvs://localhost${here}/hack1.repo#module" VERBOSITY="" 2>&1 | sed "/ no commitids before/"d

# Compare the results
# FIXME: Should be compare-all, but that function is busted.
repotool compare hack1-mirror hack1-git || echo "FAILED: Repositories do not compare equal."

echo "workflow-cvs-git: PASSED"

#end
