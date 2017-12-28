## Test comparing all named locations tags between svn and git repo

# Should be a multiple-tag, multiple-branch repository
stem=nontipcopy

# No user-serviceable parts below this line

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }
command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

#trap "rm -rf /tmp/test-repo$$-svn /tmp/test-repo$$-git /tmp/out$$" 0 12 2 15

./svn-to-svn -q -n /tmp/test-repo$$-svn <$stem.svn
reposurgeon "read <${stem}.svn" "prefer git" "rebuild /tmp/test-repo$$-git" >/tmp/out$$ 2>&1
repotool compare-all -x .svn -x .git /tmp/test-repo$$-svn /tmp/test-repo$$-git >/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >$2.chk;;
    --view)
	cat /tmp/out$$;;
esac
	      
