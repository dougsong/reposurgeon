#!/bin/sh
## Test detecting svn-to-git conversion failure

# We need to intoducd detectible content that was not in the correctly
# converted version.  Whatxvi we're testing here is the ability of
# repotool compare to notice this,
stem=vanilla
cat >/tmp/altered$$ <<EOF
Event-Number: 7
Event-Mark: :6

This is deliberately corrupted data for a blob.
EOF

# No user-serviceable parts below this line

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }
command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap 'rm -rf /tmp/test-repo$$-svn /tmp/test-repo$$-git /tmp/test-repo$$-svn-checkout /tmp/out$$ /tmp/altered' EXIT HUP INT QUIT TERM

./svn-to-svn -q -c /tmp/test-repo$$-svn /tmp/test-repo$$-svn-checkout <${stem}.svn
reposurgeon "read <${stem}.svn" "msgin --blobs </tmp/altered$$" "prefer git" "rebuild /tmp/test-repo$$-git" >/tmp/out$$ 2>&1
${REPOTOOL:-repotool} compare /tmp/test-repo$$-svn-checkout /tmp/test-repo$$-git 2>&1 | sed -e "s/$$/\$\$/"g >>/tmp/out$$


case $1 in
    --regress)
        diff --text -u repotool-compare-svn-git-failed.chk /tmp/out$$ || ( echo "$0: FAILED"; exit 1 ); ;;
    --rebuild)
	cat /tmp/out$$ >repotool-compare-svn-git-failed.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
