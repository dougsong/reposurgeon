#!/bin/sh
## Test listing tags in hg repository

command -v hg >/dev/null 2>&1 || { echo "    Skipped, hg missing."; exit 0; }
command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$' EXIT HUP INT QUIT TERM

./hg-to-fi -n /tmp/test-repo$$ < lighttag.fi
(cd /tmp/test-repo$$ >/dev/null || ( echo "$0: cd failed" >&2; exit 1 ); ${REPOTOOL:-repotool} tags /tmp/target$$) >/tmp/out$$ 2>&1
echo Return code: $? >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u repotool-tags-hg.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-tags-hg.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
#end
