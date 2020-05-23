## Test coalesce --changelog
read <<EOF
blob
mark :87000
data 15
Blob at :87000

commit refs/tags/emacs-pretest-21.0.104
mark :87001
author Gerd Moellmann <gerd@gnu.org> 994325109 +0000
committer Gerd Moellmann <gerd@gnu.org> 994325109 +0000
data 115
(specbind): Additionally record the buffer that was
current when a buffer-local or frame-local variable was bound.
M 100644 :87000 src/eval.c

blob
mark :87002
data 15
Blob at :87002

commit refs/tags/emacs-pretest-21.0.104
mark :87003
author Gerd Moellmann <gerd@gnu.org> 994325136 +0000
committer Gerd Moellmann <gerd@gnu.org> 994325136 +0000
data 26
*** empty log message ***
from :87001
M 100644 :87002 src/ChangeLog

blob
mark :87004
data 15
Blob at :87004

commit refs/tags/emacs-pretest-21.0.104
mark :87005
author Gerd Moellmann <gerd@gnu.org> 994340141 +0000
committer Gerd Moellmann <gerd@gnu.org> 994340141 +0000
data 74
(battery-update): Add help-echo.
From Pavel Jan,Bm(Bk <Pavel@Janik.cz>.
from :87003
M 100644 :87004 lisp/battery.el

blob
mark :87006
data 15
Blob at :87006

commit refs/tags/emacs-pretest-21.0.104
mark :87007
author Gerd Moellmann <gerd@gnu.org> 994340163 +0000
committer Gerd Moellmann <gerd@gnu.org> 994340163 +0000
data 26
*** empty log message ***
from :87005
M 100644 :87006 lisp/ChangeLog

blob
mark :87008
data 15
Blob at :87008

commit refs/tags/emacs-pretest-21.0.104
mark :87009
author Gerd Moellmann <gerd@gnu.org> 994340293 +0000
committer Gerd Moellmann <gerd@gnu.org> 994340293 +0000
data 58
Fix first line.  From Pavel Jan,Bm(Bk
<Pavel@Janik.cz>.
from :87007
M 100644 :87008 lisp/play/pong.el

blob
mark :87010
data 15
Blob at :87010

commit refs/tags/emacs-pretest-21.0.104
mark :87011
author Gerd Moellmann <gerd@gnu.org> 994340318 +0000
committer Gerd Moellmann <gerd@gnu.org> 994340318 +0000
data 26
*** empty log message ***
from :87009
M 100644 :87010 lisp/ChangeLog

EOF
coalesce --changelog
write -
