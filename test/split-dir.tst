## Split a commit based on a directory prefix
echo 1
verbose 1
quiet on
set svn_nobranch
read split-dir.svn
split 4 in bar
split 5 in zed
split 5 in f
split 5 in bar/
split 5 in baz
split 5 in bar
inspect
