#!/bin/sh
## Test repotool export of CVS repo

command -v cvs >/dev/null 2>&1 || { echo "    Skipped, cvs missing."; exit 0; }
command -v cvs-fast-export >/dev/null 2>&1 || { echo "    Skipped, cvs-fast-export missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$' EXIT HUP INT QUIT TERM

# Straight copy of our sample
cp -r hack1.repo/ /tmp/test-repo$$

(cd /tmp/test-repo$$ >/dev/null || (echo "$0: cd failed" >&2; exit 1); ${REPOTOOL:-repotool} export 2>&1) >/tmp/out$$ 2>&1

case $1 in
    --regress)
	# This line is a kludge to deal with the fact that the git version
	# running the tests may be old enough to not DTRT
	grep "^done" /tmp/out$$ >/dev/null 2>&1 || echo "done" >>/tmp/out$$
        diff --text -u repotool-export-cvs.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-export-cvs.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
#end
