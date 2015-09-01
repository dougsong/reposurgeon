## Test subdirectory branches
verbose 0
branchify trunk branches/* branches/subdir/*
branchify_map :branches/(.*)/:heads/\1:
read <subdir.svn
prefer git
write -
