## Test repocutter handling of binary data in a log
${REPOCUTTER:-repocutter} -q log <<EOF
Revision-number: 3640
Prop-content-length: 217
Content-length: 217

K 11
svm:headrev
V 42
e2f519d9-20a2-bc46-8705-e3bf7245ce19:3640

K 10
svn:author
V 4
robd
K 8
svn:date
V 27
2002-10-20T03:13:51.000000Z
K 7
svn:log
V 53
Part of patch contributed by Gunnar Andr� Dalsnes.

PROPS-END

Node-path: trunk/reactos/ntoskrnl/rtl/unicode.c
Node-kind: file
Node-action: change
Text-content-length: 69
Content-length: 69

Revision is 3640, file path is trunk/reactos/ntoskrnl/rtl/unicode.c.


EOF


