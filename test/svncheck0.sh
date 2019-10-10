## General test load for ancestry-chasing logic

dump=no
verbose=null
while getopts dv opt
do
    case $opt in
	d) dump=yes;;
	v) verbose=stdout;;
    esac
done

trap 'rm -fr test-repo test-checkout' 0 1 2 15 

svnaction () {
    filename=$1
    content=$2
    comment=$3
    if [ ! -f $filename ]
    then
	if [ ! -d `dirname $filename` ]
	then
	    mkdir `dirname $filename`
	    svn add `dirname $filename`
	fi
        echo "$content" >$filename
	svn add $filename
    else
        echo "$content" >$filename
    fi
    svn commit -m "$comment" $filename
}

{
set -e
make svn-branchy
cd test-checkout
# Content operations start here
svnaction "trunk/foo.txt" "Now is the time." "More example content" 
svnaction "trunk/bar.txt" "For all good men." "Example content in different file" 
svnaction "trunk/baz.txt" "to come to the aid of their country." "And in yet another file"
svn up  # Without this, the next copy does file copies.  With it, a directory copy. 
svn copy trunk branches/stable
svn commit -m "First directory copy"
svnaction "trunk/foo.txt" "Whether tis nobler in the mind." "Hamlet the Dane said this"
svnaction "trunk/bar.txt" "or to take arms against a sea of troubles" "He continued"
svnaction "trunk/baz.txt" "and by opposing end them" "The build-up"
svnaction "trunk/foo.txt" "to be,"  "Famous soliloquy begins"
svnaction "branches/foo.txt" "or not to be." "And continues"
svn up
svn copy trunk tags/1.0
svn commit -m "First tag copy"
# We're done
cd ..
} >/dev/$verbose 2>&1
if [ "$dump" = yes ]
then
    svnadmin dump -q test-repo
fi
