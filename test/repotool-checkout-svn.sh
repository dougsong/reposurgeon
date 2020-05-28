#!/bin/sh
## Test repotool checkout of svn repo

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }

trap 'rm -rf /tmp/test-svn-repo$$ /tmp/target$$ /tmp/out$$' EXIT HUP INT QUIT TERM

./svn-to-svn -q -n /tmp/test-svn-repo$$ < vanilla.svn
cd /tmp/test-svn-repo$$ || ( echo "$0: cd failed" >&2; exit 1 )
${REPOTOOL:-repotool} checkout /tmp/target$$
echo Return code: $? >/tmp/out$$
cd - >/dev/null || ( echo "$0: cd failed" >&2; exit 1 )
./dir-md5 /tmp/target$$ >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u repotool-checkout-svn.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-checkout-svn.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
#end

