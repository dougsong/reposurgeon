## Test comparing tags between svn and git repository

command -v svn >/dev/null 2>&1 || { echo "    Skipped, svn missing."; exit 0; }
command -v git >/dev/null 2>&1 || { echo "    Skipped, git missing."; exit 0; }

trap "rm -rf /tmp/test-repo$$-svn /tmp/test-repo$$-git /tmp/out$$" 0 12 2 15

# Should be a multiple-tag repository
stem=simpletag

./svn-to-svn -q -n /tmp/test-repo$$-svn <$stem.svn
reposurgeon "read <${stem}.svn" "prefer git" "rebuild /tmp/test-repo$$-git" >/tmp/out$$ 2>&1
repotool compare-tags -x .svn -x .git /tmp/test-repo$$-svn /tmp/test-repo$$-git | sed -e "s/$$/\$\$/"g >/tmp/out$$

case $1 in
    --regress)
        diff --text -u $2.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >$2.chk;;
esac
	      
