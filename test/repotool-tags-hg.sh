## Test listing tags in a Mercurial repository

trap "rm -rf /tmp/test-repo$$ /tmp/target$$" 0 12 2 15

./hg-to-fi -n /tmp/test-repo$$ < lighttag.fi
cd /tmp/test-repo$$
repotool tags /tmp/target$$; echo Return code: $?

