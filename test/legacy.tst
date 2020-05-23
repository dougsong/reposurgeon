## Legacy-ID pattern-matching
set testmode
read <<EOF
blob
mark :1
data 78
This is a test repository intended to exercise different forms of legacy IDs.

commit refs/heads/master
mark :2
author Eric S. Raymond <esr@thyrsus.com> 1354426675 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1354426675 -0500
data 45
An example dotted numeric 1.1 in a sentence.
M 100644 :1 README

blob
mark :3
data 104
This is a test repository intended to exercise different forms of legacy IDs.
Second version of README.

commit refs/heads/master
mark :4
author Eric S. Raymond <esr@thyrsus.com> 1354426758 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1354426758 -0500
data 31
End-of-sentence CVS-style 1.1.
from :2
M 100644 :3 .README

blob
mark :5
data 103
This is a test repository intended to exercise different forms of legacy IDs.
Third version of README.

commit refs/heads/master
mark :6
author Eric S. Raymond <esr@thyrsus.com> 1354426761 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1354426761 -0500
data 38
Subversion-style r123 in midsentence.
from :4
M 100644 :5 .README

blob
mark :7
data 104
This is a test repository intended to exercise different forms of legacy IDs.
Fourth version of README.

commit refs/heads/master
mark :8
author Eric S. Raymond <esr@thyrsus.com> 1354426763 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1354426763 -0500
data 39
End-of-sentence subversion-style r123.
from :6
M 100644 :7 .README

blob
mark :9
data 103
This is a test repository intended to exercise different forms of legacy IDs.
Fifth version of README.

commit refs/heads/master
mark :10
author Eric S. Raymond <esr@thyrsus.com> 1354426765 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1354426765 -0500
data 25
Bare 123 in midsentence.
from :8
M 100644 :9 .README

blob
mark :11
data 103
This is a test repository intended to exercise different forms of legacy IDs.
Sixth version of README.

commit refs/heads/master
mark :12
author Eric S. Raymond <esr@thyrsus.com> 1354426767 -0500
committer Eric S. Raymond <esr@thyrsus.com> 1354426767 -0500
data 34
End-of-sentence bare numeric 123.
from :10
M 100644 :11 .README

EOF
print Initially no sourcetype is set, so =N should be empty
set interactive
=N resolve
sourcetype cvs
print Expect 2 CVS results
=N list
sourcetype svn
print Expect 4 SVN results
=N list
