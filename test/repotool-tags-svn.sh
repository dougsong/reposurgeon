#!/bin/sh
## Test listing tags in svn repository

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$' EXIT HUP INT QUIT TERM

./svn-to-svn -q -n /tmp/test-repo$$ <simpletag.svn
(cd /tmp/test-repo$$ >/dev/null || ( echo "$0: cd failed" >&2; exit 1 ); ${REPOTOOL:-repotool} tags /tmp/target$$) >/tmp/out$$ 2>&1
echo Return code: $? >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u "$2.chk" /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >"$2.chk";;
    --view)
	cat /tmp/out$$;;
esac
	      
