## Test of index, tip, tags, history, paths, expunge and checkout
echo 1
read <simple.fi
index
tip :76
tags
history
verbose 1
paths
expunge 1..$ theory.txt
paths
verbose 0
checkout 116 foobar
!ls foobar
!rm -fr foobar
diff 101,103
manifest 101,103
manifest 116
manifest 116 ^reposurgeon
choose simple-expunges
paths sub foo
paths sup
write -

