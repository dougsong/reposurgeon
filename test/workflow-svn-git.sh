#!/bin/sh
## Test standard SVN to Git workflow

command -v svn >/dev/null 2>&1 || { echo "    Skipped, SVN missing."; exit 0; }
command -v svnadmin >/dev/null 2>&1 || { echo "    Skipped, svnadmin."; exit 0; }

set -e

TMPDIR=${TMPDIR:-/tmp}

trap 'rm -rf ${TMPDIR}/scratch$$ ${TMPDIR}/ref$$ ${TMPDIR}/out$$' EXIT HUP INT QUIT TERM

# Go to our sandbox
testdir=$(realpath .)
mkdir "${TMPDIR}/scratch$$"
cd "${TMPDIR}/scratch$$" >/dev/null || (echo "$0: cd failed" >&2; exit 1)

# Make a repository from a sample stream.
"${testdir}/svn-to-svn" -q -n vanilla-prime <"${testdir}/vanilla.svn"

# Make the workflow file.
repotool initialize -q vanilla-secundus svn git

# Mirror vanilla-prime into vanilla-secundus and invoke standard workflow
make --silent -e REMOTE_URL="file://${TMPDIR}/scratch$$/vanilla-prime" VERBOSITY="" 2>&1

# Compare the results
repotool compare-all vanilla-secundus-mirror vanilla-secundus-git || echo "FAILED: Repositories do not compare equal."

#end
