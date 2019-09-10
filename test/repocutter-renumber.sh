## Test renumbering and patching of copyfrom revisions
${REPOCUTTER:-repocutter} -q -r 0:3,5:17 select <branchreplace.svn | ${REPOCUTTER:-repocutter} -q renumber


