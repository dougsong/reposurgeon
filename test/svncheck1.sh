#!/bin/sh
## Test non-propagation of executable bit by copy to file
# Must be run in reposurgeon/test directory
#
# Perform file copy between directories.
# Expect the resulting dump to have an add with copyfrom at
# the last commit, as opposed to a replace.  Verify that
# the file copy operation does not leave the executable bit set.

dump=no
verbose=null
while getopts dv opt
do
    case $opt in
	d) dump=yes;;
	v) verbose=stdout;;
    esac
done
shift $(($OPTIND - 1))
(
make svn-branchy
cd test-checkout/trunk
svn mkdir thisdir
svn mkdir otherdir
echo "Other file" >otherdir/otherfile.txt
svn add otherdir/otherfile.txt
svn propset svn:executable on otherdir/otherfile.txt
svn ci -m "Initial commit of example files"
svn cp otherdir/otherfile.txt thisdir
svn ci -m "Copy of otherdir/otherfile.txt to thisdir."
cd ../..
) >/dev/$verbose 2>&1
if [ "$dump" = yes ]
then
    svnadmin dump test-repo
elif ls -l test-checkout/trunk/thisdir/otherfile.txt | grep -v x
then
    echo "svncheck1.sh: executable permission not expected"
    exit 1
fi
rm -fr test-repo test-checkout
