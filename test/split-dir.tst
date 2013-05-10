## Split a commit based on a directory prefix
echo 1
verbose 1
quiet on
set svn_nobranch
read split-dir.svn
split :3 in bar
split :4 in zed
split :4 in f
split :4 in bar/
split :4 in baz
split :4 in bar
inspect
