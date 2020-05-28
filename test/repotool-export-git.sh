#!/bin/sh
## Test repotool export of git repo

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

trap 'rm -rf /tmp/test-export-repo$$ /tmp/out$$' EXIT HUP INT QUIT TERM

./fi-to-fi -n /tmp/test-export-repo$$ < simple.fi
(cd /tmp/test-export-repo$$ >/dev/null || (echo "$0: cd failed" >&2; exit 1); ${REPOTOOL:-repotool} export 2>&1) >/tmp/out$$ 2>&1

case $mode in
    --regress)
        diff --text -u --label expected --label "seen ($version)" repotool-export-git.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-export-git.chk;;
    --view)
	cat /tmp/out$$;;
esac

#end

