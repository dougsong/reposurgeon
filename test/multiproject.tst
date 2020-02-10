## Test dissection of multiproject repo
branchify project1/trunk project1/branches/* project1/tags *
branchmap :project1/trunk:heads/master: :project1/tags:tags: :project1/branches:branches:
set testmode
read <multigen.svn
branch project2 delete
prefer git
write -
