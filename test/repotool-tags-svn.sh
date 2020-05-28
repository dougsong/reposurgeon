#!/bin/sh
## Test listing tags in svn repository

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }

trap 'rm -rf /tmp/test-tags-svn-repo$$ /tmp/target$$ /tmp/out$$' EXIT HUP INT QUIT TERM

./svn-to-svn -q -n /tmp/test-tags-svn-repo$$ <simpletag.svn
(cd /tmp/test-tags-svn-repo$$ >/dev/null || ( echo "$0: cd failed" >&2; exit 1 ); ${REPOTOOL:-repotool} tags /tmp/target$$) >/tmp/out$$ 2>&1
echo Return code: $? >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u repotool-tags-svn.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-tags-svn.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
