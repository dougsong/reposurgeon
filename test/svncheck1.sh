#!/bin/sh
## Test propagation of executable bit by copy to file with rename
# Must be run in reposurgeon/test directory
#
# Perform file copy between directories.
# Expect the resulting dump to have an add with copyfrom at
# the last commit, as opposed to a replace.  Verify that
# the file copy operation leaves the executable bit set.

dump=no
verbose=null
while getopts dv opt
do
    case $opt in
	d) dump=yes;;
	v) verbose=stdout;;
	*) echo "$0: unknown flag $opt" >&2; exit 1;;
    esac
done
# shellcheck disable=2004
shift $(($OPTIND - 1))
{
make svn-branchy
cd test-checkout/trunk >/dev/null || ( echo "$0: cd failed" >&2; exit 1 )
svn mkdir targetdir
svn mkdir sourcedir
echo "Source file" >sourcedir/sourcefile.txt
svn add sourcedir/sourcefile.txt
svn propset svn:executable on sourcedir/sourcefile.txt
svn ci -m "Initial commit of example files"
svn cp sourcedir/sourcefile.txt targetdir
svn ci -m "Copy of sourcedir/sourcefile.txt to targetdir."
cd ../.. >/dev/null || ( "$0: cd failed"; exit 1 )
} >"/dev/$verbose" 2>&1
# shellcheck disable=2010
if [ "$dump" = yes ]
then
    svnadmin dump -q test-repo
elif ls -l test-checkout/trunk/targetdir/sourcefile.txt | grep x >/dev/null
then
    :
else
    echo "$0: executable permission on targetdir/sourcefile was expected"
    exit 1
fi
rm -fr test-repo test-checkout
