#!/bin/sh
## Test comparing tag between svn and git repo

# Results should be independent of what file stem this is, as
# long as it's an svn dump and has the right festure to be named by cmploc.
stem=simpletag
cmploc=tag1
cmpmode=-t

# No user-serviceable parts below this line

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }
command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$-svn /tmp/test-repo$$-svn-checkout /tmp/test-repo$$-git /tmp/out$$' EXIT HUP INT QUIT TERM

./svn-to-svn -q -c /tmp/test-repo$$-svn <${stem}.svn
reposurgeon "read <${stem}.svn" "prefer git" "rebuild /tmp/test-repo$$-git" >/tmp/out$$ 2>&1
${REPOTOOL:-repotool} compare ${cmpmode} ${cmploc} /tmp/test-repo$$-svn-checkout /tmp/test-repo$$-git | sed -e "s/$$/\$\$/"g >>/tmp/out$$ 2>&1



case $1 in
    --regress)
        diff --text -u "$2.chk" /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >"$2.chk";;
    --view)
	cat /tmp/out$$;;
esac
	      
