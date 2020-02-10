## Create example multi-project repository

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
    # This version on svnaction does filenames or directories 
    case $1 in
	*/)
	    directory=$1
	    comment=${2:-$1 creation}
	    if [ ! -d "$directory" ]
	    then
		mkdir $directory
		svn add $directory
	    fi
	    svn commit -m "$comment"
	;;
	*)
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
	    svn commit -m "$comment"
	;;
    esac
}

{
set -e
make svn-flat
cd test-checkout
# Content operations start here
svnaction project1/
svnaction project1/trunk/
svnaction project1/branches/
svnaction project1/tags/
svnaction "project1/trunk/foo.txt" "Now is the time." "Example content" 
svnaction "project1/trunk/bar.txt" "For all good men." "Example content in different file" 
svnaction "project1/trunk/baz.txt" "to come to the aid of their country." "And in yet another file"
svn up  # Without this, the next copy does file copies.  With it, a directory copy. 
svn copy project1/trunk project1/branches/stable
svn commit -m "First directory copy"
svnaction project2/
svnaction project2/trunk/
svnaction project2/branches/
svnaction project2/tags/
svnaction "project2/trunk/foo.txt" "Whether tis nobler in the mind." "Hamlet the Dane said this"
svnaction "project2/trunk/bar.txt" "or to take arms against a sea of troubles" "He continued"
svnaction "project2/trunk/baz.txt" "and by opposing end them" "The build-up"
svnaction "project2/trunk/foo.txt" "to be,"  "Famous soliloquy begins"
svnaction "project2/trunk/foo.txt" "or not to be." "And continues"
svn up
svn copy project2/trunk project2/tags/1.0
svn commit -m "First tag copy"
svn copy project2/trunk project1/trunk/evilcopy
svn commit -m "Example cross-project copy"
# We're done
cd ..
} >/dev/$verbose 2>&1
if [ "$dump" = yes ]
then
    svnadmin dump -q test-repo | sed '1a\
 ## Multi-project repository example
'
fi
