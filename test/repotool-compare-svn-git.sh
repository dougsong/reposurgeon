#!/bin/sh
## Test comparing master between svn and git repo

# Results should be independent of what file stem this is, as
# long as it's an svn dump.
stem=vanilla

# No user-serviceable parts below this line

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }
command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$-svn /tmp/test-repo$$-git /tmp/test-repo$$-svn-checkout /tmp/out$$' EXIT HUP INT QUIT TERM

./svn-to-svn -q -c /tmp/test-repo$$-svn /tmp/test-repo$$-svn-checkout <${stem}.svn
reposurgeon "read <${stem}.svn" "prefer git" "rebuild /tmp/test-repo$$-git" >/tmp/out$$ 2>&1
${REPOTOOL:-repotool} compare /tmp/test-repo$$-svn-checkout /tmp/test-repo$$-git | sed -e "s/$$/\$\$/"g >>/tmp/out$$ 2>&1


case $1 in
    --regress)
        diff --text -u "$2.chk" /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >"$2.chk";;
    --view)
	cat /tmp/out$$;;
esac
	      
