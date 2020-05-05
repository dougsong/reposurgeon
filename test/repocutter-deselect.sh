#!/bin/sh
## Test deselection
${REPOCUTTER:-repocutter} -q -r 4:HEAD deselect <vanilla.svn

