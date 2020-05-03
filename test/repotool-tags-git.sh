#!/bin/sh
## Test listing tags in git repository

command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$' EXIT HUP INT QUIT TERM

./fi-to-fi -n /tmp/test-repo$$ < lighttag.fi
(cd /tmp/test-repo$$ || (echo "$0: cd failed" >&2; exit 1); ${REPOTOOL:-repotool} tags /tmp/target$$) >/tmp/out$$ 2>&1
echo Return code: $? >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u repotool-tags-git.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-tags-git.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
