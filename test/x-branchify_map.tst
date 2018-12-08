## Test branchify_map command
verbose 0
branchify ProjA/trunk ProjB/trunk
branchify_map @^([^/]+)/(.*)/$@heads/\1_\2@
read <x-branchify_map.svn
prefer git
write -

