## Test comparing tags between git and hg repo
# Reproduces https://gitlab.com/esr/reposurgeon/issues/39

trap "rm -rf /tmp/test-repo$$-git /tmp/test-repo$$-hg /tmp/out$$" 0 12 2 15

# Should be independent of what strem file we speciy here.
stem=lighttag

# No user-serviceable parts below this line

command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }
command -v hg >/dev/null 2>&1 || { echo "    Skipped, hg missing."; exit 0; }

./fi-to-fi -n /tmp/test-repo$$-git <${stem}.fi
./hg-to-fi -n /tmp/test-repo$$-hg <${stem}.fi
repotool compare-tags -x .git -x .hg -x .hgtags /tmp/test-repo$$-git /tmp/test-repo$$-hg | sed -e "s/$$/\$\$/"g >/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >$2.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
