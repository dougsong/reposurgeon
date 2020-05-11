#!/bin/sh
## Test comparing tags between git and hg repo
# Reproduces https://gitlab.com/esr/reposurgeon/issues/39

trap 'rm -rf /tmp/test-repo$$-git /tmp/test-repo$$-hg /tmp/out$$' EXIT HUP INT QUIT TERM

# Should be independent of what strem file we speciy here.
stem=lighttag

# No user-serviceable parts below this line

command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }
command -v hg >/dev/null 2>&1 || { echo "    Skipped, hg missing."; exit 0; }

./fi-to-fi -n /tmp/test-repo$$-git <${stem}.fi
./hg-to-fi -n /tmp/test-repo$$-hg <${stem}.fi
${REPOTOOL:-repotool} compare-tags -x '.git|.hg|.hgtags' /tmp/test-repo$$-git /tmp/test-repo$$-hg 2>&1 | sed -e "s/$$/\$\$/"g >/tmp/out$$ 2>&1

case $1 in
    --regress)
        diff --text -u "repotool-compare-tags-git-hg.chk" /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >"repotool-compare-tags-git-hg.chk";;
    --view)
	cat /tmp/out$$;;
esac
	      
