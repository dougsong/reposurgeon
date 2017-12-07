#!/bin/sh
# Must be run in reposurgeon/test directory
#
# Perform file copy between directories.
# Expect the resulting dump to have an add with copyfrom at
# the last commit, as opposed to a replace.
(
make svn-branchy
cd test-checkout/trunk
svn mkdir thisdir
echo "This file" >thisdir/thisfile.txt
svn mkdir otherdir
echo "Other file" >otherdir/otherfile.txt
svn add thisdir/thisfile.txt
svn add otherdir/otherfile.txt
svn ci -m "Initial commit of example files"
svn cp otherdir/otherfile.txt thisdir/file.txt
svn ci -m "Replace thisdir/file.txt with a copy of otherdir/otherfile.txt."
cd ../..
) >/dev/null 2>&1
svnadmin dump test-repo
rm -fr test-repo test-checkout
