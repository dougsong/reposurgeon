## Test retract and re-creation of branch tag.
# Yes, it's confusing that tag directories are being branch-mapped. 
branchify_map :tags/(.*)/:tags/\1:
read <fleetwood.svn
prefer git
write -
