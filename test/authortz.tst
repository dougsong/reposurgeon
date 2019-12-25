## Check that deduction of commtter TZ doesn't leak.
read <authortz.svn
authors read <<EOF
jsm28 = Test Author <test@author.example> America/Los_Angeles
EOF
changelogs
prefer git
write -
