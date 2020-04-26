#!/bin/sh
## Test repotool export of git repo

command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

mode=${1:---regress}

# shellcheck disable=SC2046
set -- $(git --version)
version="$3"
if [ "$version" != "2.20.1" ] && [ "$mode" = "--regress" ]
then
    echo "SKIPPED - sensitive to Git version skew, seeing unsupported $version"
    exit 0
fi

trap 'rm -rf /tmp/test-repo$$ /tmp/out$$' EXIT HUP INT QUIT TERM

./fi-to-fi -n /tmp/test-repo$$ < simple.fi
(cd /tmp/test-repo$$ >/dev/null || (echo "$0: cd failed" >&2; exit 1); ${REPOTOOL:-repotool} export 2>&1) >/tmp/out$$ 2>&1

case $mode in
    --regress)
        diff --text -u --label expected --label "seen ($version)" repotool-export-git.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >repotool-export-git.chk;;
    --view)
	cat /tmp/out$$;;
esac

#end

