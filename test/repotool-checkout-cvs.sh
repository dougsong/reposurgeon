## Test repotool checkout of CVS repo

command -v cvs >/dev/null 2>&1 || { echo "    Skipped, cvs missing."; exit 0; }

trap "rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$" 0 12 2 15

set -e	# So we'll crap out if hack-repo does not exist
cp -r hack1.repo/ /tmp/test-repo$$
cd /tmp/test-repo$$
repotool checkout /tmp/target$$; echo Return code: $? >/tmp/out$$
cd - >/dev/null
rm -rf /tmp/target$$/CVS/	# CVS internal use, and contents are different every time
./dir-md5 /tmp/target$$  >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >$2.chk;;
    --view)
	cat /tmp/out$$;;
esac

#end
