## Test repocutter patching of mergeinfo references in renumber
${REPOCUTTER:-repocutter} -q renumber <<EOF
SVN-fs-dump-format-version: 2

UUID: 7a7f4d26-e363-49a8-afdf-ef5f249c7278

Revision-number: 0
Prop-content-length: 56
Content-length: 56

K 8
svn:date
V 27
2012-11-06T12:57:02.495463Z
PROPS-END

Revision-number: 1
Prop-content-length: 125
Content-length: 125

K 8
svn:date
V 27
2012-11-06T12:57:02.596436Z
K 7
svn:log
V 25
default repository layout
K 10
svn:author
V 5
db48x
PROPS-END

Node-path: branches
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
Prop-content-length: 126
Content-length: 126

K 8
svn:date
V 27
2012-11-06T12:57:04.687219Z
K 7
svn:log
V 26
trunk development proceeds
K 10
svn:author
V 5
db48x
PROPS-END

Node-path: trunk/README
Node-kind: file
Node-action: add
Prop-content-length: 10
Text-content-length: 94
Text-content-md5: 66760f04bb3ec9129227765a900c6cb7
Text-content-sha1: aa3b8c4fffcbd104b99fbfdbf9dadf554742f323
Content-length: 104

PROPS-END
this svn repository is for testing reposurgeon's way of dealing with svn:mergeinfo properties


Node-path: trunk/VERSION
Node-kind: file
Node-action: add
Prop-content-length: 10
Text-content-length: 5
Text-content-md5: 89f3822117a6da8c74ad7d283786de45
Text-content-sha1: e43b691cc2d26f910c466674e6f747554ce488ea
Content-length: 15

PROPS-END
0.99


Node-path: trunk/src
Node-kind: file
Node-action: add
Prop-content-length: 10
Text-content-length: 20
Text-content-md5: a992fbf885c23cd43b873f9b6b4f07d1
Text-content-sha1: d4751405250715b8d7cfb73445f4815b2df9dc6a
Content-length: 30

PROPS-END
feature development


Revision-number: 4
Prop-content-length: 131
Content-length: 131

K 7
svn:log
V 31
create a release branch for 1.0
K 10
svn:author
V 5
db48x
K 8
svn:date
V 27
2012-11-06T12:57:08.920527Z
PROPS-END

Node-path: branches/v1.0
Node-kind: dir
Node-action: add
Node-copyfrom-rev: 3
Node-copyfrom-path: trunk


Revision-number: 5
Prop-content-length: 126
Content-length: 126

K 8
svn:date
V 27
2012-11-06T12:57:11.009151Z
K 7
svn:log
V 26
trunk development proceeds
K 10
svn:author
V 5
db48x
PROPS-END

Node-path: trunk/VERSION
Node-kind: file
Node-action: change
Text-content-length: 4
Text-content-md5: d39d8df974f8d45e3d23499dc20ea763
Text-content-sha1: 49aec2b9c6b091a17f0f4a82f5f4549121bd0124
Content-length: 4

1.1


Node-path: trunk/src
Node-kind: file
Node-action: change
Text-content-length: 60
Text-content-md5: 861d248fa2226b7f722b9e9069fb5922
Text-content-sha1: 334d457e6b85135e26dcd7a967163c819334d18a
Content-length: 60

feature development
feature development
feature development


Revision-number: 6
Prop-content-length: 142
Content-length: 142

K 7
svn:log
V 42
emergency bugfix for v1.0, releasing 1.0.1
K 10
svn:author
V 5
db48x
K 8
svn:date
V 27
2012-11-06T12:57:13.113053Z
PROPS-END

Node-path: branches/v1.0/VERSION
Node-kind: file
Node-action: change
Text-content-length: 6
Text-content-md5: ee7ab3e7e15d1e00ec001ca33b4571f1
Text-content-sha1: cfc5fe3a1d6f7e773eb019d04681697648d23e76
Content-length: 6

1.0.1


Node-path: branches/v1.0/src
Node-kind: file
Node-action: change
Text-content-length: 47
Text-content-md5: bb8e96610102281c22a0bcbbbdb9a3ae
Text-content-sha1: 34397d41ff585e97f4794ce247db9148119008dc
Content-length: 47

feature development
feature development
bugfix


Revision-number: 7
Prop-content-length: 160
Content-length: 160

K 8
svn:date
V 27
2012-11-06T12:57:15.290908Z
K 7
svn:log
V 60
merge bugfixes from 1.0.1 into trunk, bumping version to 1.2
K 10
svn:author
V 5
db48x
PROPS-END

Node-path: trunk
Node-kind: dir
Node-action: change
Prop-content-length: 53
Content-length: 53

K 13
svn:mergeinfo
V 18
/branches/v1.0:4-6
PROPS-END


Node-path: trunk/VERSION
Node-kind: file
Node-action: change
Text-content-length: 4
Text-content-md5: add9573d0bdbe6b511957d850d7ceb80
Text-content-sha1: 6d69fa1724f4a439d489ee56aa0c22fdd41c632c
Content-length: 4

1.2


Node-path: trunk/src
Node-kind: file
Node-action: change
Text-content-length: 67
Text-content-md5: eaf7b8609ae6f1a2c1f0032bf28648bd
Text-content-sha1: 262a62a90fa4a79b5f51891d8a1dc184089ff489
Content-length: 67

feature development
feature development
feature development
bugfix


Revision-number: 8
Prop-content-length: 126
Content-length: 126

K 8
svn:date
V 27
2012-11-06T12:57:17.395735Z
K 7
svn:log
V 26
trunk development proceeds
K 10
svn:author
V 5
db48x
PROPS-END

Node-path: trunk/VERSION
Node-kind: file
Node-action: change
Text-content-length: 4
Text-content-md5: 84b17206d983a7430710b2a1f8ae52b8
Text-content-sha1: e350bf129ed3e8455fb310efe23a787adfdf9fb4
Content-length: 4

1.3


Node-path: trunk/src
Node-kind: file
Node-action: change
Text-content-length: 87
Text-content-md5: 842df0e74d9bd00f23515de785eaf623
Text-content-sha1: add43e2e50fe6c994394eb730f998a9aab19dc79
Content-length: 87

feature development
feature development
feature development
bugfix
feature development


Revision-number: 9
Prop-content-length: 142
Content-length: 142

K 7
svn:log
V 42
emergency bugfix for v1.0, releasing 1.0.2
K 10
svn:author
V 5
db48x
K 8
svn:date
V 27
2012-11-06T12:57:19.495644Z
PROPS-END

Node-path: branches/v1.0/VERSION
Node-kind: file
Node-action: change
Text-content-length: 6
Text-content-md5: 14607822426d690390607bb48a124f66
Text-content-sha1: 880d9396e60cb9e65a3af230f9467412553b6d50
Content-length: 6

1.0.2


Node-path: branches/v1.0/src
Node-kind: file
Node-action: change
Text-content-length: 54
Text-content-md5: 6b2fd8641052c00d43c2c4a730119114
Text-content-sha1: ddabd589a81ce1893d8a97fd995977168b29f81f
Content-length: 54

feature development
feature development
bugfix
bugfix


Revision-number: 10
Prop-content-length: 142
Content-length: 142

K 8
svn:date
V 27
2012-11-06T12:57:21.582865Z
K 7
svn:log
V 42
emergency bugfix for v1.0, releasing 1.0.3
K 10
svn:author
V 5
db48x
PROPS-END

Node-path: branches/v1.0/VERSION
Node-kind: file
Node-action: change
Text-content-length: 6
Text-content-md5: db007b32b16e26f01cae59f75e492284
Text-content-sha1: 8fbc549835992841cbef4232a1d5b86780d3ad5b
Content-length: 6

1.0.3


Node-path: branches/v1.0/src
Node-kind: file
Node-action: change
Text-content-length: 61
Text-content-md5: 49044ada8e86b7ab6d1134418d23227c
Text-content-sha1: b6e38b365fe013ebf1a39b72a6c341174659f5ee
Content-length: 61

feature development
feature development
bugfix
bugfix
bugfix


Revision-number: 11
Prop-content-length: 160
Content-length: 160

K 8
svn:date
V 27
2012-11-06T12:57:23.732297Z
K 7
svn:log
V 60
merge bugfixes from 1.0.3 into trunk, bumping version to 1.4
K 10
svn:author
V 5
db48x
PROPS-END

Node-path: trunk
Node-kind: dir
Node-action: change
Prop-content-length: 57
Content-length: 57

K 13
svn:mergeinfo
V 22
/branches/v1.0:4-6,8-9
PROPS-END


Node-path: trunk/VERSION
Node-kind: file
Node-action: change
Text-content-length: 4
Text-content-md5: 25198dbbb5f787214992c13a596f5751
Text-content-sha1: 2e1d6e852c9d321bb37cb601ab2a6d97e323153e
Content-length: 4

1.4


Node-path: trunk/src
Node-kind: file
Node-action: change
Text-content-length: 94
Text-content-md5: 49b1ff1a8c39053a5b7e3750caeedbf8
Text-content-sha1: 6d509dd0109e4271106eaf8d9b7a7bc25b43bf77
Content-length: 94

feature development
feature development
feature development
bugfix
feature development
bugfix


Revision-number: 12
Prop-content-length: 113
Content-length: 113

K 7
svn:log
V 13
release party
K 10
svn:author
V 5
db48x
K 8
svn:date
V 27
2012-11-06T12:57:23.824840Z
PROPS-END

Node-path: trunk/VERSION
Node-kind: file
Node-action: change
Text-content-length: 4
Text-content-md5: 3cf918272ffa5de195752d73f3da3e5e
Text-content-sha1: 7959c969e092f2a5a8604e2287807ac5b1b384ad
Content-length: 4

2.0


Node-path: trunk/src
Node-kind: file
Node-action: change
Text-content-length: 114
Text-content-md5: 8f8e5641a0f580a4dec2329ed0c84ef9
Text-content-sha1: dee645e9b02d2ef4855f9cb894674be7b86b9222
Content-length: 114

feature development
feature development
feature development
bugfix
feature development
bugfix
feature development


Revision-number: 13
Prop-content-length: 131
Content-length: 131

K 8
svn:date
V 27
2012-11-06T12:57:25.948537Z
K 7
svn:log
V 31
create a release branch for 2.0
K 10
svn:author
V 5
db48x
PROPS-END

Node-path: branches/v2.0
Node-kind: dir
Node-action: add
Node-copyfrom-rev: 12
Node-copyfrom-path: trunk


Revision-number: 14
Prop-content-length: 126
Content-length: 126

K 8
svn:date
V 27
2012-11-06T12:57:28.038481Z
K 7
svn:log
V 26
trunk development proceeds
K 10
svn:author
V 5
db48x
PROPS-END

Node-path: trunk/VERSION
Node-kind: file
Node-action: change
Text-content-length: 4
Text-content-md5: 66fc3b29b9f8fdf7454d23906d40a7e4
Text-content-sha1: da51fa3f73e561cf695cbcf67e9d92d801038cd8
Content-length: 4

2.1


Node-path: trunk/src
Node-kind: file
Node-action: change
Text-content-length: 134
Text-content-md5: 4c0921a4789296f2ac5f869f83e384de
Text-content-sha1: 4f5ca2b14b8a7484d2400d8e0ea3b9f249c637cf
Content-length: 134

feature development
feature development
feature development
bugfix
feature development
bugfix
feature development
feature development


Revision-number: 15
Prop-content-length: 142
Content-length: 142

K 8
svn:date
V 27
2012-11-06T12:57:30.127978Z
K 7
svn:log
V 42
emergency bugfix for v2.0, releasing 2.0.1
K 10
svn:author
V 5
db48x
PROPS-END

Node-path: branches/v2.0/VERSION
Node-kind: file
Node-action: change
Text-content-length: 6
Text-content-md5: 311f5bba9037308eec0e9f402dd38009
Text-content-sha1: 1fb7be12efaa1608dc63e784e33082ae0ac7919b
Content-length: 6

2.0.1


Node-path: branches/v2.0/src
Node-kind: file
Node-action: change
Text-content-length: 121
Text-content-md5: 1458a3030bcb4cfdcd2b5403ea51e44d
Text-content-sha1: dfea01d33d89cf9a0f5d9e1652e50c9fb9ff8e69
Content-length: 121

feature development
feature development
feature development
bugfix
feature development
bugfix
feature development
bugfix


Revision-number: 16
Prop-content-length: 160
Content-length: 160

K 7
svn:log
V 60
merge bugfixes from 2.0.1 into trunk, bumping version to 2.2
K 10
svn:author
V 5
db48x
K 8
svn:date
V 27
2012-11-06T12:57:32.274887Z
PROPS-END

Node-path: trunk
Node-kind: dir
Node-action: change
Prop-content-length: 75
Content-length: 75

K 13
svn:mergeinfo
V 40
/branches/v1.0:4-6,8-9
/branches/v2.0:15
PROPS-END




Node-path: trunk/VERSION
Node-kind: file
Node-action: change
Text-content-length: 4
Text-content-md5: f292756b084a24dc24839d86b04853c9
Text-content-sha1: 1c4be7c8663cf9d0ac34ad639d7e22d548f1e6bc
Content-length: 4

2.2


Node-path: trunk/src
Node-kind: file
Node-action: change
Text-content-length: 141
Text-content-md5: f395844a86a89975faaf9dac28eb9e8d
Text-content-sha1: 5108c0e645427c046e903a97e040cddafee0f58f
Content-length: 141

feature development
feature development
feature development
bugfix
feature development
bugfix
feature development
feature development
bugfix


EOF


