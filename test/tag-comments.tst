## Test tag comment handling
read <<EOF
blob
mark :1
data 23
This is a sample file.

reset refs/heads/master
commit refs/heads/master
mark :2
committer esr <esr> 1322671432 +0000
data 16
First revision.
M 100644 :1 README

blob
mark :3
data 68
This is a sample file.

This is our first line of modified content.

commit refs/heads/master
mark :4
committer esr <esr> 1322671521 +0000
data 17
Second revision.
from :2
M 100644 :3 README

blob
mark :5
data 114
This is a sample file.

This is our first line of modified content.

This is our second line of modified content.

commit refs/heads/master
mark :6
committer esr <esr> 1322671565 +0000
data 16
Third revision.
from :4
M 100644 :5 README

tag root
from :2
tagger esr <esr> 1322671315 +0000
data 122
A vanilla repository - standard layout, linear history, no tags, no branches. 

[[Tag from root commit at Subversion r1]]

tag emptycommit-5
from :6
tagger esr <esr> 1323084440 +0000
data 151
Adding a property setting.

[[Tag from zero-fileop commit at Subversion r5:
<NodeAction: r5 change file 'trunk/README' properties=[('foo', 'bar')]>
]]

tag no-comment
from :4
tagger esr <esr> 1322671316 +0000
data 0

tag with-comment
from :6
tagger esr <esr> 1322671317 +0000
data 19
this is a test tag

EOF
tags
names
write -
