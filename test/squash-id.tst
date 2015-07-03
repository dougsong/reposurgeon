## Test use of legacy IDs after a squash --delete
read <squash-id.svn
<3> squash --delete --quiet
<4> append "appended to legacy rev 4 comment\n"
prefer git
write -
