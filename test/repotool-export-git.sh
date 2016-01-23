## Test repotool export of git repo

command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap "rm -rf /tmp/test-repo$$ /tmp/out$$" 0 12 2 15

./fi-to-fi -n /tmp/test-repo$$ < simple.fi
(cd /tmp/test-repo$$ >/dev/null; repotool export) | diff --text -u --label simple.fi simple.fi --label repotool-export - >/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >$2.chk;;
esac

#end
