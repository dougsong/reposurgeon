read <<SVNDUMP-EOF
SVN-fs-dump-format-version: 2
 ##  Check that bogus mergeinfo doesn't crash reposurgeon

UUID: 104126b2-20fb-11ea-8903-474d39b52133

Revision-number: 0
Prop-content-length: 56
Content-length: 56

K 8
svn:date
V 27
2019-12-17T18:28:47.005710Z
PROPS-END

Revision-number: 1
Prop-content-length: 128
Content-length: 128

K 10
svn:author
V 6
jmyers
K 8
svn:date
V 27
2019-12-17T18:29:23.950784Z
K 7
svn:log
V 27
Create directory structure.
PROPS-END

Node-path: branches
Node-kind: dir
Node-action: add
Prop-content-length: 10
Content-length: 10

PROPS-END


Node-path: tags
Node-kind: dir
Node-action: add
Prop-content-length: 10
Content-length: 10

PROPS-END


Node-path: trunk
Node-kind: dir
Node-action: add
Prop-content-length: 10
Content-length: 10

PROPS-END


Revision-number: 2
Prop-content-length: 109
Content-length: 109

K 10
svn:author
V 6
jmyers
K 8
svn:date
V 27
2019-12-17T18:29:45.543342Z
K 7
svn:log
V 9
Add foo.

PROPS-END

Node-path: trunk/foo
Node-kind: file
Node-action: add
Text-content-md5: 154d45611081dc7858043af2d9554d6f
Text-content-sha1: fc4c444d36872cb10cffdc34ee2cbd8c2c820f80
Prop-content-length: 10
Text-content-length: 9
Content-length: 19

PROPS-END
file foo


Revision-number: 3
Prop-content-length: 116
Content-length: 116

K 10
svn:author
V 6
jmyers
K 8
svn:date
V 27
2019-12-17T18:30:10.444365Z
K 7
svn:log
V 15
Create branch.

PROPS-END

Node-path: branches/somebranch
Node-kind: dir
Node-action: add
Node-copyfrom-rev: 2
Node-copyfrom-path: trunk


Revision-number: 4
Prop-content-length: 119
Content-length: 119

K 10
svn:author
V 6
jmyers
K 8
svn:date
V 27
2019-12-17T18:32:22.856848Z
K 7
svn:log
V 18
Merge from trunk.

PROPS-END

Node-path: branches/somebranch
Node-kind: dir
Node-action: change
Prop-content-length: 57
Content-length: 57

K 13
svn:mergeinfo
V 22
/trunk:1-2-3,7-5,2-,-3
PROPS-END


SVNDUMP-EOF
prefer git
write -
