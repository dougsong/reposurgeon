#!/bin/sh
## Test repotool initialize with cvs source and git dest

mkdir /tmp/test-workdir$$
cd /tmp/test-workdir$$ || ( echo "$0: cd failed"; exit 1 )
${REPOTOOL:-repotool} initialize xyzzy cvs git >/tmp/out$$
echo Return code: $? >>/tmp/out$$
# shellcheck disable=2064
cd - >/dev/null || ( echo "$0: cd failed"; exit 1 )
./dir-md5 /tmp/test-workdir$$ >>/tmp/out$$

case $1 in
    --regress)
        diff --text -u repotool-initialize-cvs-git.chk /tmp/out$$ || exit 1; ;;
    --rebuild)
	cat /tmp/out$$ >repotool-initialize-cvs-git.chk;;
    --view)
	cat /tmp/out$$;;
esac

st=$?
if [ $st -eq 0 ]; then
	rm -rf /tmp/test-workdir$$ /tmp/out$$
fi

exit $st

#end

