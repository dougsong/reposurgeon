## Test repotool export of hg repo

command -v hg >/dev/null 2>&1 || { echo "    Skipped, hg missing."; exit 0; }

hg >/dev/null 2>/dev/null || echo "    Skipped, hg missing." && exit 0

trap "rm -rf /tmp/test-repo$$ /tmp/out$$" 0 12 2 15

./hg-to-fi -n /tmp/test-repo$$ < testrepo2.fi
(cd /tmp/test-repo$$ >/dev/null; repotool export) | ./hg-to-fi | sed -e 1d -e '/^#legacy-id/d' | diff --text -u --label testrepo2.fi testrepo2.fi --label repotool-export - >/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >$2.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
#end

