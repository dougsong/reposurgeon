## Test of index, tip, tags, history, paths, expunge and checkout
set echo
read <simple.fi
~=B index
:76 tip
tags
paths
1..$ expunge theory.txt
paths
116 checkout foobar
!ls foobar
!rm -fr foobar
101,103 diff
101,103 manifest 
116 manifest 
116 manifest /^reposurgeon/
paths sub foo
paths sup
:2 setfield comment "The quick brown fox jumped over the lazy dog.\n"
:2 setperm 100755 rs
# Stream enough parts to verify the last two operations
:2 inspect
