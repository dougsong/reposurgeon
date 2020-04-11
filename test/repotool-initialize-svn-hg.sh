#!/bin/sh
## Test repotool initialize with svn source and hg dest

mkdir /tmp/test-workdir$$
cd /tmp/test-workdir$$ >/dev/null || ( echo "$0: cd failed" >&2; exit 1 )
${REPOTOOL:-repotool} initialize xyzzy svn hg >/tmp/out$$
echo Return code: $? >>/tmp/out$$
cd - >/dev/null >/dev/null || ( echo "$0: cd failed" >&2; exit 1 )
./dir-md5 /tmp/test-workdir$$ >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u repotool-initialize-svn-hg.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >repotool-initialize-svn-hg.chk;;
    --view)
	cat /tmp/out$$;;
esac

st=$?
if [ $st -eq 0 ]; then
	rm -rf /tmp/test-workdir$$ /tmp/out$$
fi

exit $st

#end

