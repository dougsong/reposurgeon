## Split a commit based on a directory prefix
echo 1
verbose 1
quiet on
# Expect the split on zed to fail
read --nobranch <split-dir.svn
:2 split by bar
:5 split by zed
:5 split by f
inspect
