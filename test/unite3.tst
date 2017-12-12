## Test unite of 3 repositories
read <<EOF
blob
mark :1
data 49
hello from repo1 on Wed Nov  8 00:16:10 UTC 2017

reset refs/heads/master
commit refs/heads/master
mark :2
author repo1 <sample-repo1@example.com> 1510100170 -0500
committer repo1 <sample-repo1@example.com> 1510100170 -0500
data 17
initial revision
M 100644 :1 hello.txt

reset refs/heads/master
from :2

EOF
rename hello1
read <<EOF
blob
mark :1
data 49
hello from repo2 on Wed Nov  8 00:16:12 UTC 2017

reset refs/heads/master
commit refs/heads/master
mark :2
author repo2 <sample-repo2@example.com> 1510100172 -0500
committer repo2 <sample-repo2@example.com> 1510100172 -0500
data 17
initial revision
M 100644 :1 hello.txt

reset refs/heads/master
from :2

EOF
rename hello2
read <<EOF
blob
mark :1
data 49
hello from repo3 on Wed Nov  8 00:16:14 UTC 2017

reset refs/heads/master
commit refs/heads/master
mark :2
author repo3 <sample-repo3@example.com> 1510100174 -0500
committer repo3 <sample-repo3@example.com> 1510100174 -0500
data 17
initial revision
M 100644 :1 hello.txt

reset refs/heads/master
from :2

EOF
rename hello3
unite hello1 hello2 hello3
write -

