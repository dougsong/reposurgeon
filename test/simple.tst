## Test of index, tip, tags, history, paths, expunge and checkout
echo 1
read <simple.fi
index
:76 tip
tags
history
verbose 1
paths
1..$ expunge theory.txt
paths
verbose 0
116 checkout foobar
!ls foobar
!rm -fr foobar
101,103 diff
101,103 manifest 
116 manifest 
116 manifest ^reposurgeon
choose simple-expunges
paths sub foo
paths sup
:28 setfield comment "The quick brown fox jumped over the lazy dog.\n"
:51 setperm 100755 theory.txt
# Stream the repo
write -

