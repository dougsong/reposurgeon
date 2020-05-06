#!/bin/sh
## Test repotool export of svn repo

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$ /tmp/out$$' EXIT HUP INT QUIT TERM

# Make a repository from a sample stream.
./svn-to-svn -q -n /tmp/test-repo$$ <vanilla.svn

# This test can fail spuriously due to format skew.  Kevin Caswick
# explains:
# > Note: Test repotool export of svn repo fails on svnadmin, version
# > 1.6.11 as the dump is sorted differently, moving svn:log before
# > svn:author instead of after svn:date. It works fine on svnadmin,
# > version 1.8.10.
(cd /tmp/test-repo$$ >/dev/null || (echo "$0: cd failed" >&2; exit 1); ${REPOTOOL:-repotool} export) >/tmp/out$$

case $1 in
    --regress)
        diff --text -u repotool-export-svn.chk /tmp/out$$  || (echo "$0: cd failed" >&2; exit 1) || (echo "$0: FAILED"; exit 1); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-export-svn.chk;;
    --view)
	cat /tmp/out$$;;
esac

#end

