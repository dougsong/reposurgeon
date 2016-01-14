## Test repotool export of CVS repo

trap "rm -rf /tmp/test-repo$$ /tmp/target$$ /tmp/out$$" 0 12 2 15

cp -r hack1.repo/module/ /tmp/test-repo$$
(cd /tmp/test-repo$$ >/dev/null; repotool export) >/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ ;;
esac
	      
#end
