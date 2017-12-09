## Test propagation of executable bit by directory copy

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
dir=$(pwd)
svnadmin create $dir/test-repo
svn co file://$dir/test-repo test-checkout
cd test-checkout
mkdir trunk
svn add trunk
svn commit -m "Create trunk."
cd trunk
mkdir dir1
echo "file" > dir1/file
svn add dir1
svn commit -m "Create dir1/file."
svn propset svn:executable '*' dir1/file
svn commit -m "Make dir1/file executable."
svn cp dir1 dir2
svn commit -m "Copy dir1 to dir2."
ls -l dir1/file dir2/file
cd ../..
} >/dev/$verbose 2>&1
if [ "$dump" = yes ]
then
    svnadmin dump -q test-repo
elif ls -l test-checkout/trunk/dir2/file | grep x >/dev/null
then
    :
else
    echo "$0: executable permission was expected"
    exit 1
fi
rm -fr test-repo test-checkout
