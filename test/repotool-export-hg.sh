#!/bin/sh
## Test repotool export of hg repo

command -v hg >/dev/null 2>&1 || { echo "    Skipped, hg missing."; exit 0; }

hg >/dev/null 2>/dev/null || echo "    Skipped, hg missing." && exit 0

trap 'rm -rf /tmp/test-repo$$ /tmp/out$$' EXIT HUP INT QUIT TERM

./hg-to-fi -n /tmp/test-repo$$ < testrepo2.fi
(cd /tmp/test-repo$$ >/dev/null || ( echo "$0: cd failed" >&2; exit 1 ); ${REPOTOOL:-repotool} export 2>&1) | ./hg-to-fi | sed -e 1d -e '/^#legacy-id/d' | diff --text -u --label testrepo2.fi testrepo2.fi --label repotool-export - >/tmp/out$$ 2>&1

case $1 in
    --regress)
        diff --text -u repotool-export-hg.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >repotool-export-hg.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
#end

