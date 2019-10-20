## Test branchmap command
branchify ProjA/trunk ProjB/trunk
branchmap @^([^/]+)/(.*)/$@heads/\1_\2@
read <branchmap.svn
prefer git
write -

