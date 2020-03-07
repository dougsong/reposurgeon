#!/bin/sh
## Test repotool checkout of Mercurial repo

command -v hg >/dev/null 2>&1 || { echo "    Skipped, hg missing."; exit 0; }
command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$' EXIT HUP INT QUIT TERM

./hg-to-fi -n /tmp/test-repo$$ < simple.fi
cd /tmp/test-repo$$ || (echo "$0: cd failed" >&2; exit 1)
${REPOTOOL:-repotool} checkout /tmp/target$$
echo Return code: $? >/tmp/out$$
cd - >/dev/null || (echo "$0: cd failed" >&2; exit 1)
./dir-md5 /tmp/target$$ >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u "$2.chk" /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >"$2.chk";;
    --view)
	cat /tmp/out$$;;
esac
	      
#end
