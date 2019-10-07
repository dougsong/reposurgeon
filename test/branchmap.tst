## Test branchmap command
verbose 0
branchify ProjA/trunk ProjB/trunk
branchmap @^([^/]+)/(.*)/$@heads/\1_\2@
read <branchmap.svn
prefer git
write -

