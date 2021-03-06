#!/bin/sh
## Test listing tags in CVS repository

command -v cvs >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }

trap 'rm -rf /tmp/test-tags-cvs-repo$$ /tmp/target$$ /tmp/out$$' EXIT HUP INT QUIT TERM

# Straight copy of our sample
cp -r hack1.repo/ /tmp/test-tags-cvs-repo$$

(cd /tmp/test-tags-cvs-repo$$ >/dev/null || ( echo "$0: cd failed" >&2; exit 1 ); ${REPOTOOL:-repotool} tags /tmp/target$$) >/tmp/out$$ 2>&1
echo Return code: $? >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u repotool-tags-cvs.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-tags-cvs.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
