## Test repotool export of CVS repo

command -v cvs >/dev/null 2>&1 || { echo "    Skipped, cvs missing."; exit 0; }
command -v cvs-fast-export >/dev/null 2>&1 || { echo "    Skipped, cvs-fast-export missing."; exit 0; }

trap "rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$" 0 12 2 15

cp -r hack1.repo/ /tmp/test-repo$$
(cd /tmp/test-repo$$ >/dev/null; ${REPOTOOL:-repotool} export) >/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >$2.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
#end
