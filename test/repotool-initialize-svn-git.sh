#!/bin/sh
## Test repotool initialize with svn source and git dest

mkdir /tmp/test-workdir$$
(cd /tmp/test-workdir$$ >/dev/null || ( echo "$0: cd failed" >&2; exit 1 ); ${REPOTOOL:-repotool} initialize xyzzy svn git >/tmp/out$$; echo Return code: $? >>/tmp/out$$)
./dir-md5 /tmp/test-workdir$$ >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u repotool-initialize-svn-git.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >repotool-initialize-svn-git.chk;;
    --view)
	cat /tmp/out$$;;
esac

st=$?
if [ $st -eq 0 ]; then
	rm -rf /tmp/test-workdir$$ /tmp/out$$
fi

exit $st

#end

