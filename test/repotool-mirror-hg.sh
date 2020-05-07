#!/bin/sh
## Test repotool mirror of hg repo

command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

mode=${1:---regress}

# shellcheck disable=SC2046
set -- $(git --version)
version="$3"
if [ "$version" != "2.25.1" ] && [ "$mode" = "--regress" ]
then
    # 2.20.1 emits terminal resets that 2.25.1 does not.
    echo "SKIPPED - sensitive to Git version skew, seeing unsupported $version"
    exit 0
fi

# Build an example repo
./hg-to-fi -n /tmp/test-repo$$ < testrepo2.fi
# Then exercise the mirror code to make a copy of it, and dump it.
${REPOTOOL:-repotool} mirror "file://tmp/test-repo$$" /tmp/mirror$$
(cd /tmp/mirror$$ >/dev/null || (echo "$0: cd failed" >&2; exit 1); ${REPOTOOL:-repotool} export) >/tmp/out$$ 2>&1

case $mode in
    --regress)
	# This line is a kludge to deal with the fact that the git version
	# running the tests may be old enough to not DTRT
	grep "^done" /tmp/out$$ >/dev/null 2>&1 || echo "done" >>/tmp/out$$
        diff --text -u repotool-mirror-hg.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	grep "^done" /tmp/out$$ >/dev/null 2>&1 || echo "done" >>/tmp/out$$
	cat /tmp/out$$ >repotool-mirror-hg.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
#end



