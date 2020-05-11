#!/bin/sh
## Test comparing tags between svn and git repo

# Should be a multiple-tag repository
stem=simpletag

# No user-serviceable parts below this line

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }
command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$-svn /tmp/test-repo$$-git /tmp/out$$' EXIT HUP INT QUIT TERM

./svn-to-svn -q -n /tmp/test-repo$$-svn <"$stem.svn"
reposurgeon "read <${stem}.svn" "prefer git" "rebuild /tmp/test-repo$$-git" >/tmp/out$$ 2>&1
${REPOTOOL:-repotool} compare-tags /tmp/test-repo$$-svn /tmp/test-repo$$-git | sed -e "s/$$/\$\$/"g >/tmp/out$$ 2>&1

case $1 in
    --regress)
        diff --text -u repotool-compare-tags-svn-git.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-compare-tags-svn-git.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
