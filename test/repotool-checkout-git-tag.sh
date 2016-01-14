## Test repotool checkout of git repo at tag

command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap "rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$" 0 12 2 15

./fi-to-fi -n /tmp/test-repo$$ < simple.fi
cd /tmp/test-repo$$
repotool checkout /tmp/target$$ lightweight-sample
echo Return code: $? >/tmp/out$$
cd - >/dev/null
./dir-md5 /tmp/target$$ >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >$2.chk;;
esac
	      
#end

