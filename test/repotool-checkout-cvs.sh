#!/bin/sh
## Test repotool checkout of CVS repo

command -v cvs >/dev/null 2>&1 || { echo "    Skipped, cvs missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$' EXIT HUP INT QUIT TERM

set -e	# So we'll crap out if hack-repo does not exist
cp -r hack1.repo/ /tmp/test-repo$$
(cd /tmp/test-repo$$ >/dev/null; ${REPOTOOL:-repotool} checkout /tmp/target$$; echo Return code: $? >/tmp/out$$ 2>&1)
rm -rf /tmp/target$$/CVS/	# CVS internal use, and contents are different every time
./dir-md5 /tmp/target$$  >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u repotool-checkout-cvs.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-checkout-cvs.chk;;
    --view)
	cat /tmp/out$$;;
esac

#end
