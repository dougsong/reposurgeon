## Test diff
read <<EOF
blob
mark :1
data 20
1234567890123456789

commit refs/heads/master
mark :2
committer Ralf Schlatterbeck <rsc@runtux.com> 0 +0000
data 14
First commit.
M 100644 :1 README

blob
mark :3
data 20
0123456789012345678

blob
mark :4
data 4
foo

commit refs/heads/master
mark :5
committer Ralf Schlatterbeck <rsc@runtux.com> 10 +0000
data 38
Second commit: modify README, add foo
from :2
M 100644 :3 README
M 100644 :4 foo

commit refs/heads/master
mark :6
committer Ralf Schlatterbeck <rsc@runtux.com> 20 +0000
data 38
Third commit: keep README, delete foo
from :5
D foo

EOF
:2,:5 diff
:2,:5 diff
:5,:6 diff
:5,:2 diff
