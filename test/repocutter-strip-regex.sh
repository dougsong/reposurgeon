#!/bin/sh
## Test strip subcommand to skeletonize selected paths
${REPOCUTTER:-repocutter} -q <vanilla-2file.svn strip file1
