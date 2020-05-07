#!/bin/sh
## Test repotool export of svn repo

# /tmp/test-repo-fubar has a fixed name because it gets generated
# into the checkfile as the value of the svn:sync-from-url
# property.  If that changes on each run it's going to cause
# spurious test failures

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }

trap 'rm -rf /tmp/test-repo-fubar /tmp/out$$ /tmp/mirror$$' EXIT HUP INT QUIT TERM

# Make a repository from a sample stream.
./svn-to-svn -q -n /tmp/test-repo-fubar <vanilla.svn
# Then exercise the mirror code to make a copy of it.
${REPOTOOL:-repotool} mirror file:///tmp/test-repo-fubar /tmp/mirror$$

# This test can fail spuriously due to format skew.  Kevin Caswick
# explains:
# > Note: Test repotool export of svn repo fails on svnadmin, version
# > 1.6.11 as the dump is sorted differently, moving svn:log before
# > svn:author instead of after svn:date. It works fine on svnadmin,
# > version 1.8.10.
(cd /tmp/mirror$$ >/dev/null || ( echo "$0: cd failed" >&2; exit 1 ); ${REPOTOOL:-repotool} export) >/tmp/out$$

# Why this test, and only this one, generates randomly varying UUIDs is unknown
case $1 in
    --regress)
        sed </tmp/out$$ -e '/UUID:/d' | diff --text -u repotool-mirror-svn.chk - || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	sed </tmp/out$$ -e '/UUID:/d' >repotool-mirror-svn.chk;;
    --view)
	cat /tmp/out$$;;
esac

#end

