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
    esac
done
shift $(($OPTIND - 1))
{
make svn-branchy
cd test-checkout/trunk
svn mkdir targetdir
svn mkdir sourcedir
echo "Source file" >sourcedir/sourcefile.txt
svn add sourcedir/sourcefile.txt
svn propset svn:executable on sourcedir/sourcefile.txt
svn ci -m "Initial commit of example files"
svn cp sourcedir/sourcefile.txt targetdir
svn ci -m "Copy of sourcedir/sourcefile.txt to targetdir."
cd ../..
} >/dev/$verbose 2>&1
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
