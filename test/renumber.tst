## Test the renumber command
# The gap in numbering is between 12 and 23
read <<EOF
blob
mark :1
data 129
This is a simple repository containing several lightweight tags.
It is inytended for tests of tag rename and deletion semantics.

reset refs/tags/first-tag
commit refs/tags/first-tag
mark :2
author Eric S. Raymond <esr@thyrsus.com> 1390369942 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1390369942 -0500
data 16
Initial commit.
M 100644 :1 README

blob
mark :3
data 128
This is a simple repository containing several lightweight tags.
It is intended for tests of tag rename and deletion semantics.

commit refs/tags/first-tag
mark :4
author Eric S. Raymond <esr@thyrsus.com> 1390370009 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1390370009 -0500
data 51
Fix a typo. Which produces a useful spacer commit.
from :2
M 100644 :3 README

blob
mark :5
data 170
This is a simple repository containing several lightweight tags.
It is intended for tests of tag rename and deletion semantics.

First tag should point at this revision.

commit refs/tags/first-tag
mark :6
author Eric S. Raymond <esr@thyrsus.com> 1390370078 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1390370078 -0500
data 32
We add a first lightweight tag.
from :4
M 100644 :5 README

blob
mark :7
data 205
This is a simple repository containing several lightweight tags.
It is intended for tests of tag rename and deletion semantics.

First tag should point at this revision.

Now we add another spacer commit.

commit refs/tags/second-tag
mark :8
author Eric S. Raymond <esr@thyrsus.com> 1390370218 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1390370218 -0500
data 25
This is a spacer commit.
from :6
M 100644 :7 README

blob
mark :9
data 248
This is a simple repository containing several lightweight tags.
It is intended for tests of tag rename and deletion semantics.

First tag should point at this revision.

Now we add another spacer commit.

Second tag should point at this revision.

commit refs/tags/second-tag
mark :10
author Eric S. Raymond <esr@thyrsus.com> 1390370324 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1390370324 -0500
data 24
Second tag points here.
from :8
M 100644 :9 README

blob
mark :11
data 283
This is a simple repository containing several lightweight tags.
It is intended for tests of tag rename and deletion semantics.

First tag should point at this revision.

Now we add another spacer commit.

Second tag should point at this revision.

Npw we add another spacer commit.

commit refs/tags/third-tag
mark :12
author Eric S. Raymond <esr@thyrsus.com> 1390370440 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1390370440 -0500
data 24
A second spacer commit.
from :10
M 100644 :11 README

blob
mark :23
data 325
This is a simple repository containing several lightweight tags.
It is intended for tests of tag rename and deletion semantics.

First tag should point at this revision.

Now we add another spacer commit.

Second tag should point at this revision.

Npw we add another spacer commit.

Third tag should point at this revision.

commit refs/tags/third-tag
mark :24
author Eric S. Raymond <esr@thyrsus.com> 1390370544 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1390370544 -0500
data 23
Third tag points here.
from :12
M 100644 :23 README

blob
mark :25
data 360
This is a simple repository containing several lightweight tags.
It is intended for tests of tag rename and deletion semantics.

First tag should point at this revision.

Now we add another spacer commit.

Second tag should point at this revision.

Npw we add another spacer commit.

Third tag should point at this revision.

And we add a third spacer commit.

commit refs/heads/master
mark :26
author Eric S. Raymond <esr@thyrsus.com> 1390370664 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1390370664 -0500
data 21
Third spacer commit.
from :24
M 100644 :25 README

reset refs/heads/master
from :26

EOF
renumber
print If there is not a commit :13 right after :12, something is busted
write -



