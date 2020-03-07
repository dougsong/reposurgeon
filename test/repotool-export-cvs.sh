#!/bin/sh
## Test repotool export of CVS repo

command -v cvs >/dev/null 2>&1 || { echo "    Skipped, cvs missing."; exit 0; }
command -v cvs-fast-export >/dev/null 2>&1 || { echo "    Skipped, cvs-fast-export missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$' EXIT HUP INT QUIT TERM

cp -r hack1.repo/ /tmp/test-repo$$
(cd /tmp/test-repo$$ >/dev/null || (echo "$0: cd failed" >&2; exit 1); ${REPOTOOL:-repotool} export 2>&1) >/tmp/out$$ 2>&1

case $1 in
    --regress)
        diff --text -u "$2.chk" /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >"$2.chk";;
    --view)
	cat /tmp/out$$;;
esac
	      
#end
