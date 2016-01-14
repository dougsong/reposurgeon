## Test comparing tags between git and Mercurial repository
# Reproduces https://gitlab.com/esr/reposurgeon/issues/39

trap "rm -rf /tmp/test-repo$$-git /tmp/test-repo$$-hg /tmp/out$$" 0 12 2 15

./fi-to-fi -n /tmp/test-repo$$-git < lighttag.fi
./hg-to-fi -n /tmp/test-repo$$-hg < lighttag.fi
repotool compare-tags -x .git -x .hg -x .hgtags /tmp/test-repo$$-git /tmp/test-repo$$-hg | sed -e "s/$$/\$\$/"g >/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ ;;
esac
	      
