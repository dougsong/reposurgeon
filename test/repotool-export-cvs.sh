## Test repotool export of CVS repo

trap "rm -rf /tmp/test-repo$$ /tmp/target$$" 0 12 2 15

cp -r hack1.repo/module/ /tmp/test-repo$$
(cd /tmp/test-repo$$ >/dev/null; repotool export)

#end
