## Test repotool export of svn repo

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }

trap "rm -rf /tmp/test-repo$$ /tmp/out$$" 0 12 2 15

./svn-to-svn -q -n /tmp/test-repo$$ <vanilla.svn
(cd /tmp/test-repo$$ >/dev/null; repotool export) >/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >$2.chk;;
esac

#end

