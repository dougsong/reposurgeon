## Test backreference substitution in filter --regexp
read <<EOF
blob
mark :1
data 14
Example file.

reset refs/heads/master
commit refs/heads/master
mark :2
author  Chris P. Bacon <cpb@example.com> 1588089692 -0700
committer Chris P. Bacon <cpb@example.com> 1588089692 -0700
data 22
s12345 s45678 s21456

M 100644 :1 README
EOF
# EXPECT 'rb:\1' should be 'rb:12345' (the substitution /s(\d+)/\1/)
(=C) filter --regex /s(\d+)/rb:\1/1
(=C) msgout
write -
