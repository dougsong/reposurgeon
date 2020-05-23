## Tag reference test
read <<EOF
blob
mark :1
data 35
Not an obfuscated C contest entry.

blob
mark :2
data 46
The quick brown fox jumped over the lazy dog.

commit refs/heads/master
mark :3
committer foo <foo> 101800 +0000
data 13
First commit
M 100644 :1 bar.c
M 100644 :2 foo.c
M 100644 inline .gitignore
data 199
# CVS default ignores begin
tags
TAGS
.make.state
.nse_depinfo
*~
\#*
.#*
,*
_$*
*$
*.old
*.bak
*.BAK
*.orig
*.rej
.del-*
*.a
*.olb
*.o
*.obj
*.so
*.exe
*.Z
*.elc
*.ln
core
# CVS default ignores end


reset refs/tags/first
from :3

commit refs/heads/master
mark :4
committer foo <foo> 102400 +0000
data 14
Second commit
from :3
D bar.c

reset refs/tags/tag
from :4

reset refs/heads/master
from :4

EOF
set echo
<master> inspect
<tag> inspect
<first> inspect
