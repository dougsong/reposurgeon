## Test matching on author name
read <<EOF
blob
mark :376857
data 16
Blob at :376857

blob
mark :376858
data 16
Blob at :376858

blob
mark :376859
data 16
Blob at :376859

blob
mark :376860
data 16
Blob at :376860

reset refs/heads/xwidget^0
commit refs/heads/xwidget
mark :376861
author =Constantin Kulikov <zxnotdead@gmail.com> 1356371359 +0100
committer martin rudalics <rudalics@gmx.at> 1356371359 +0100
data 310
Allow function as value of initial-buffer-choice (Bug#13251).

* startup.el (initial-buffer-choice): Allow function as value
(Bug#13251).
(command-line-1): Handle case where initial-buffer-choice
specifies a function.
* server.el (server-execute): Handle case where
initial-buffer-choice specifies a function.
M 100644 :376857 etc/NEWS
M 100644 :376858 lisp/ChangeLog
M 100644 :376859 lisp/server.el
M 100644 :376860 lisp/startup.el

EOF
set interactive
/Kulikov/a resolve Should match
/mumble/a resolve Should not match
