## Test listing tags in a git repository

trap "rm -rf /tmp/test-repo$$ /tmp/target$$" 0 12 2 15

./fi-to-fi -n /tmp/test-repo$$ < lighttag.fi
cd /tmp/test-repo$$
repotool tags /tmp/target$$; echo Return code: $?

