## Test repotool export of git repo

trap "rm -rf /tmp/test-repo$$" 0 12 2 15

./hg-to-fi -n /tmp/test-repo$$ < testrepo2.fi
(cd /tmp/test-repo$$ >/dev/null; repotool export) | ./hg-to-fi | sed -e 1d -e '/^#legacy-id/d' | diff --text -u --label testrepo2.fi testrepo2.fi --label repotool-export -

#end

