## Test subdirectory branches
branchify trunk branches/* branches/subdir/*
branchmap :branches/(.*)/:heads/\1:
read <subdir.svn
prefer git
<subdir/mybranch> list
write -
