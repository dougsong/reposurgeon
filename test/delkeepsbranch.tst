## Check that no branch or tag is lost by delete --tagback
read <<EOF
commit refs/heads/master
mark :1
committer Eric S. Raymond <esr@thyrsus.com> 1289147634 -0500
data 14
First commit.
M 644 inline README
data 37
This is a test file in a dummy repo.


commit refs/tags/v1
mark :2
committer Eric S. Raymond <esr@thyrsus.com> 1289147718 -0500
data 40
Test of a tag with a file modification.
from :1
M 644 inline README
data 42
This is a modification of that test file.


commit refs/tags/v2
mark :3
committer Eric S. Raymond <esr@thyrsus.com> 1289147740 -0500
data 46
Test of another tag with a file modification.
from :2
M 644 inline README
data 48
This is another modification of that test file.

EOF
inspect
:2,:3 delete --tagback
inspect
