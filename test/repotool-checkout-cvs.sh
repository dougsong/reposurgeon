## Test repotool checkout of git repo

command -v cvs >/dev/null 2>&1 || { echo "    Skipped, cvs missing."; exit 0; }

trap "rm -rf /tmp/test-repo$$ /tmp/target$$" 0 12 2 15

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
esac

#end
