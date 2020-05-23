## Regression test authors write format
# Expected format: USER = Name <USER@DOMAIN>
read <<EOF
blob
mark :1
data 3
Hi

reset refs/heads/master
commit refs/heads/master
mark :2
author Kevin O. Grover <kevin@kevingrover.net> 1472305515 -0700
committer Kevin O. Grover <kevin@kevingrover.net> 1472305515 -0700
data 13
Just Testing
M 100644 :1 file.txt

reset refs/heads/master
from :2

EOF
authors write
