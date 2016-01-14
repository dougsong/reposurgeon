## Test listing tags in a git repository

command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap "rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$" 0 12 2 15

./fi-to-fi -n /tmp/test-repo$$ < lighttag.fi
(cd /tmp/test-repo$$; repotool tags /tmp/target$$) >/tmp/out$$
echo Return code: $? >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >$2.chk;;
esac
	      
