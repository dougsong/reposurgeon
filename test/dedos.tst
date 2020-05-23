## Test filter --dedos
read <<EOF
blob
mark :1
data 21
1234567890123456789

commit refs/heads/master
mark :2
committer Ralf Schlatterbeck <rsc@runtux.com> 0 +0000
data 15
First commit.
M 100644 :1 README

blob
mark :3
data 21
0123456789012345678

commit refs/heads/master
mark :4
committer Ralf Schlatterbeck <rsc@runtux.com> 10 +0000
data 16
Second commit.
from :2
M 100644 :3 README

EOF
set interactive
1..$ filter --dedos
clear interactive
write -
