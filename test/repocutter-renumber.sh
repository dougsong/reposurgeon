## Test renumbering and patching of copyfrom revisions
${REPOCUTTER:-repocutter} -q -r 0:2,4:17 select <branchreplace.svn | ${REPOCUTTER:-repocutter} -q renumber


