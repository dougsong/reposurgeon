#!/bin/sh
## Test repotool mirror of CVS repo

# This is how we detect we're in Gitlab CI.
if [ -z "${USER}" ]
then
    echo "SKIPPED - ssh is blocked in CI"
    exit 0
fi

command -v cvs >/dev/null 2>&1 || { echo "    Skipped, cvs missing."; exit 0; }
command -v cvs-fast-export >/dev/null 2>&1 || { echo "    Skipped, cvs-fast-export missing."; exit 0; }

trap 'rm -rf /tmp/mirror$$ /tmp/out$$' EXIT HUP INT QUIT TERM

# Then exercise the mirror code to make a copy of it, and dump it.
${REPOTOOL:-repotool} mirror "cvs://localhost${PWD}/hack1.repo#module" /tmp/mirror$$
(cd /tmp/mirror$$ >/dev/null || (echo "$0: cd failed" >&2; exit 1); ${REPOTOOL:-repotool} export 2>&1) >/tmp/out$$ 2>&1

case $1 in
    --regress)
	# This line is a kludge to deal with the fact that the git version
	# running the tests may be old enough to not DTRT
	grep "^done" /tmp/out$$ >/dev/null 2>&1 || echo "done" >>/tmp/out$$
        diff --text -u repotool-mirror-cvs.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-mirror-cvs.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
#end



