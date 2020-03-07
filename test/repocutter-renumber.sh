#!/bin/sh
## Test renumbering and patching of copyfrom revisions
${REPOCUTTER:-repocutter} -q -r 0:5,7:17 select <branchreplace.svn | ${REPOCUTTER:-repocutter} -q renumber


