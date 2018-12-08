## Test subdirectory branches
verbose 0
branchify trunk branches/* branches/subdir/*
branchify_map :branches/(.*)/:heads/\1:
read <x-subdir.svn
prefer git
<subdir/mybranch> list
write -
