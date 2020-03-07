#!/bin/sh
## Test that without modifiers it's a faithful copy
stem=vanilla	# Any Subversion dump we plug in here should make empty output
#shellcheck disable=SC2094
${REPOCUTTER:-repocutter} -q select <"${stem}.svn" | diff "${stem}.svn" -


